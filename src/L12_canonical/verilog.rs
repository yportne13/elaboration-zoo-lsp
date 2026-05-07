//! Verilog code generation from the HDL module IR.
//!
//! After elaboration, the `mutable_map["module"]` contains a `module` struct
//! (a list of `Module` structs, each holding a `Vec[Expr]`).
//! This module walks that representation and emits synthesizable Verilog.

use std::collections::HashSet;

use super::*;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Emit Verilog for the current module in the Infer's mutable state.
///
/// Returns a `String` containing the Verilog module.
/// If `"module"` is not present in the mutable map, returns an empty string.
pub fn emit_verilog(infer: &Infer, decl: &Decl, lvl: Lvl) -> String {
    let guard = infer.mutable_map.read().unwrap();
    let module_val = match guard.get("module") {
        Some(v) => v.clone(),
        None => return String::new(),
    };
    drop(guard);

    let module_tm = infer.quote(decl, lvl, &module_val);
    let modules = collect_modules(&module_tm);

    let mut out = String::new();
    for m in &modules {
        out.push_str(&emit_one_module(m));
        out.push('\n');
    }
    out
}

// ---------------------------------------------------------------------------
// Intermediate representation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum HdlExpr {
    Create(String),
    Binary(Box<HdlExpr>, String, Box<HdlExpr>),
    Assign(Box<HdlExpr>, Box<HdlExpr>),
    When(Box<HdlExpr>, Box<HdlExpr>, Option<Box<HdlExpr>>),
    Switch(Box<HdlExpr>, Vec<(Vec<HdlExpr>, HdlExpr)>),
}

#[derive(Debug, Clone)]
struct HdlModule {
    name: String,
    exprs: Vec<HdlExpr>,
}

// ---------------------------------------------------------------------------
// Tm walkers
// ---------------------------------------------------------------------------

/// Extract a String literal from a Tm.
fn extract_string(tm: &Rc<Tm>) -> String {
    match tm.as_ref() {
        Tm::LiteralIntro(s) => s.data.clone(),
        _ => "?".to_string(),
    }
}

/// Find a named field in a SumCase datas list.
fn find_field<'a>(datas: &'a [(Span<SmolStr>, Rc<Tm>, Icit)], name: &str) -> Option<&'a Rc<Tm>> {
    datas.iter().find(|(n, _, _)| n.data == name).map(|(_, v, _)| v)
}

/// Walk a Vec<T> (dependent vector) represented as List-like cons/nil SumCase.
/// Returns items in **reverse** order (the Vec stores items prepended).
fn collect_vec<F, T>(tm: &Rc<Tm>, f: &F) -> Vec<T>
where
    F: Fn(&Rc<Tm>) -> T,
{
    match tm.as_ref() {
        Tm::SumCase { case_name, datas, .. } => match case_name.data.as_str() {
            "nil" => vec![],
            "cons" => {
                // cons[l: Nat](x: A, xs: Vec[A] l)
                let head = &datas[1].1; // x: A  (skip implicit l=datas[0])
                let tail = &datas[2].1; // xs
                let mut rest = collect_vec(tail, f);
                rest.push(f(head)); // reverse order: Vec prepends, we push
                rest
            }
            _ => vec![],
        },
        _ => vec![],
    }
}

/// Convert a Tm representing an Expr to HdlExpr.
fn tm_to_hdl(tm: &Rc<Tm>) -> HdlExpr {
    match tm.as_ref() {
        Tm::SumCase { case_name, datas, .. } => match case_name.data.as_str() {
            "create" => {
                let name = datas.first()
                    .map(|d| extract_string(&d.1))
                    .unwrap_or_else(|| "?".to_string());
                HdlExpr::Create(name)
            }
            "binary" => {
                let lhs = Box::new(tm_to_hdl(find_field(datas, "lhs").unwrap()));
                let op = find_field(datas, "op")
                    .map(|t| extract_string(t))
                    .unwrap_or_else(|| "?".to_string());
                let rhs = Box::new(tm_to_hdl(find_field(datas, "rhs").unwrap()));
                HdlExpr::Binary(lhs, op, rhs)
            }
            "assign" => {
                let lhs = Box::new(tm_to_hdl(find_field(datas, "lhs").unwrap()));
                let rhs = Box::new(tm_to_hdl(find_field(datas, "rhs").unwrap()));
                HdlExpr::Assign(lhs, rhs)
            }
            "when" => {
                let cond = Box::new(tm_to_hdl(find_field(datas, "cond").unwrap()));
                let body = Box::new(tm_to_hdl(find_field(datas, "body").unwrap()));
                let else_body = find_field(datas, "elseBody").and_then(|t| match t.as_ref() {
                    Tm::SumCase { case_name, .. } if case_name.data == "none" => None,
                    Tm::SumCase { datas, .. } if case_name.data == "some" => {
                        Some(Box::new(tm_to_hdl(&datas[0].1)))
                    }
                    _ => None,
                });
                HdlExpr::When(cond, body, else_body)
            }
            "switch" => {
                let value = Box::new(tm_to_hdl(find_field(datas, "value").unwrap()));
                let cases_tm = find_field(datas, "cases").unwrap();
                let cases = collect_vec(cases_tm, &|case_tm| {
                    // Each case is the body Expr (simplified for now)
                    (vec![], tm_to_hdl(case_tm))
                });
                HdlExpr::Switch(value, cases)
            }
            _ => {
                // Not an Expr constructor – maybe it's a direct reference
                HdlExpr::Create(format!("sig_{}", case_name.data))
            }
        },
        _ => {
            // Fallback: treat unknown forms as signal references
            HdlExpr::Create(format!("?{}", super::pretty::pretty_tm(0, List::new(), tm)))
        }
    }
}

/// Walk the top-level `module` value and collect the current `HdlModule`.
///
/// The module state accumulates via `change_mutable` which creates new `module`
/// structs linked through the Vec tail. We only take the HEAD Module of the
/// outermost Vec (the latest snapshot that has all expressions).
fn collect_modules(top_tm: &Rc<Tm>) -> Vec<HdlModule> {
    // top_tm is `module::module.mk(num, data)`
    let data_tm = match top_tm.as_ref() {
        Tm::SumCase { datas, .. } => find_field(datas, "data"),
        _ => None,
    };

    let data_tm = match data_tm {
        Some(t) => t.clone(),
        None => return vec![],
    };

    // data_tm is a Vec<Module>. We only care about the HEAD (latest snapshot).
    match data_tm.as_ref() {
        Tm::SumCase { case_name, datas, .. } if case_name.data == "cons" => {
            // cons[l: Nat](x: Module, xs: Vec[Module] l)
            let head_module_tm = &datas[1].1; // x: Module (the latest)

            // Extract module name from head
            let name = match head_module_tm.as_ref() {
                Tm::SumCase { datas, .. } => {
                    find_field(datas, "name")
                        .map(|t| extract_string(t))
                        .unwrap_or_else(|| "unnamed".to_string())
                }
                _ => "unnamed".to_string(),
            };

            // Extract expr vec from head
            let exprs_tm = match head_module_tm.as_ref() {
                Tm::SumCase { datas, .. } => {
                    find_field(datas, "expr").cloned()
                }
                _ => None,
            };

            let exprs = match exprs_tm {
                Some(t) => {
                    let raw = collect_vec(&t, &tm_to_hdl);
                    // Reverse to get creation order (Vec prepends, so latest first)
                    raw.into_iter().rev().collect()
                }
                None => vec![],
            };

            vec![HdlModule { name, exprs }]
        }
        Tm::SumCase { case_name, .. } if case_name.data == "nil" => vec![],
        _ => {
            // Maybe it's a single Module directly
            let name = match data_tm.as_ref() {
                Tm::SumCase { datas, .. } => find_field(datas, "name")
                    .map(|t| extract_string(t))
                    .unwrap_or_else(|| "unnamed".to_string()),
                _ => "unnamed".to_string(),
            };
            let exprs_tm = match data_tm.as_ref() {
                Tm::SumCase { datas, .. } => find_field(datas, "expr").cloned(),
                _ => None,
            };
            let exprs = match exprs_tm {
                Some(t) => {
                    let raw = collect_vec(&t, &tm_to_hdl);
                    raw.into_iter().rev().collect()
                }
                None => vec![],
            };
            vec![HdlModule { name, exprs }]
        }
    }
}

// ---------------------------------------------------------------------------
// Verilog emission
// ---------------------------------------------------------------------------

/// Collect all signal names referenced in a list of HdlExprs (in order).
fn collect_signals(exprs: &[HdlExpr]) -> Vec<String> {
    let mut wires = Vec::new();
    let mut seen = HashSet::new();
    // Walk expressions in reverse to get creation order (exprs are prepended)
    for e in exprs.iter().rev() {
        collect_signals_rec(e, &mut wires, &mut seen);
    }
    wires
}

fn collect_signals_rec(e: &HdlExpr, wires: &mut Vec<String>, seen: &mut HashSet<String>) {
    match e {
        HdlExpr::Create(name) => {
            if seen.insert(name.clone()) {
                wires.push(name.clone());
            }
        }
        HdlExpr::Binary(lhs, _op, rhs) => {
            collect_signals_rec(lhs, wires, seen);
            collect_signals_rec(rhs, wires, seen);
        }
        HdlExpr::Assign(lhs, rhs) => {
            collect_signals_rec(lhs, wires, seen);
            collect_signals_rec(rhs, wires, seen);
        }
        HdlExpr::When(cond, body, else_body) => {
            collect_signals_rec(cond, wires, seen);
            collect_signals_rec(body, wires, seen);
            if let Some(eb) = else_body {
                collect_signals_rec(eb, wires, seen);
            }
        }
        HdlExpr::Switch(value, cases) => {
            collect_signals_rec(value, wires, seen);
            for (_pat, body) in cases {
                collect_signals_rec(body, wires, seen);
            }
        }
    }
}

/// Emit a single HdlExpr as Verilog (recursively).
fn emit_expr(e: &HdlExpr, indent: usize, in_assign: bool) -> String {
    let pad = "  ".repeat(indent);
    match e {
        HdlExpr::Create(name) => {
            // Sanitize name for Verilog
            sanitize_name(name)
        }
        HdlExpr::Binary(lhs, op, rhs) => {
            match op.as_str() {
                // Reduction operators (unary)
                "andR" => format!("&{}", emit_expr(lhs, 0, false)),
                "orR" => format!("|{}", emit_expr(lhs, 0, false)),
                "xorR" => format!("^{}", emit_expr(lhs, 0, false)),
                // Bit access
                "msb" => format!("{}[MSB]", emit_expr(lhs, 0, false)),
                "lsb" => format!("{}[0]", emit_expr(lhs, 0, false)),
                // Concatenation
                "##" => format!("{{{}, {}}}", emit_expr(lhs, 0, false), emit_expr(rhs, 0, false)),
                // Regular binary ops
                _ => {
                    let vop = verilog_op(op);
                    format!("({} {} {})", emit_expr(lhs, 0, false), vop, emit_expr(rhs, 0, false))
                }
            }
        }
        HdlExpr::Assign(lhs, rhs) => {
            if in_assign {
                format!("{} = {}", emit_expr(lhs, 0, false), emit_expr(rhs, 0, false))
            } else {
                format!("{}assign {} = {};", pad, emit_expr(lhs, 0, false), emit_expr(rhs, 0, false))
            }
        }
        HdlExpr::When(cond, body, else_body) => {
            let mut s = format!("{}if ({}) begin\n", pad, emit_expr(cond, 0, false));
            s.push_str(&emit_expr(body, indent + 1, true));
            s.push_str(&format!("\n{}end", pad));
            if let Some(eb) = else_body {
                s.push_str(&format!(" else begin\n"));
                s.push_str(&emit_expr(eb, indent + 1, true));
                s.push_str(&format!("\n{}end", pad));
            }
            s
        }
        HdlExpr::Switch(value, cases) => {
            let mut s = format!("{}case ({})\n", pad, emit_expr(value, 0, false));
            for (i, (_pat, body)) in cases.iter().enumerate() {
                s.push_str(&format!("{}  /* case {} */\n", pad, i));
                s.push_str(&emit_expr(body, indent + 2, true));
                s.push('\n');
            }
            s.push_str(&format!("{}endcase", pad));
            s
        }
    }
}

fn verilog_op(op: &str) -> &str {
    match op {
        "+" | "+^" => "+",
        "-" | "-^" => "-",
        "*" => "*",
        "&" => "&",
        "|" => "|",
        "^" => "^",
        "<<" => "<<",
        ">>" => ">>",
        "<" => "<",
        "<=" => "<=",
        ">" => ">",
        ">=" => ">=",
        "===" => "==",
        "=/=" => "!=",
        other => other,
    }
}

fn sanitize_name(name: &str) -> String {
    name.replace(|c: char| !c.is_alphanumeric() && c != '_', "_")
}

/// Emit a single HdlModule as a complete Verilog module.
fn emit_one_module(m: &HdlModule) -> String {
    let wires = collect_signals(&m.exprs);
    let mut out = String::new();

    // Find which signals are assigned to (outputs)
    let mut assigned = HashSet::new();
    for e in &m.exprs {
        if let HdlExpr::Assign(lhs, _) = e {
            if let HdlExpr::Create(name) = lhs.as_ref() {
                assigned.insert(name.clone());
            }
        }
    }

    // Module declaration
    out.push_str(&format!("module {} (\n", sanitize_name(&m.name)));
    for (i, w) in wires.iter().enumerate() {
        let comma = if i + 1 < wires.len() { "," } else { "" };
        let dir = if assigned.contains(w) { "output" } else { "input" };
        out.push_str(&format!("  {} wire {}{}\n", dir, sanitize_name(w), comma));
    }
    out.push_str(");\n\n");

    // Wire declarations
    for w in &wires {
        out.push_str(&format!("  wire {};\n", sanitize_name(w)));
    }
    out.push('\n');

    // Expressions body
    // Separate Creates (signals) from Assigns
    let has_control = m.exprs.iter().any(|e| matches!(e, HdlExpr::When(..) | HdlExpr::Switch(..)));

    if has_control {
        out.push_str("  always @* begin\n");
        for e in &m.exprs {
            match e {
                HdlExpr::Assign(..) | HdlExpr::When(..) | HdlExpr::Switch(..) => {
                    out.push_str(&format!("  {}\n", emit_expr(e, 1, true)));
                }
                HdlExpr::Create(_) | HdlExpr::Binary(..) => {
                    // Skip standalone creates/binary (they're in assignments)
                }
            }
        }
        out.push_str("  end\n");
    } else {
        // Pure continuous assignments
        for e in &m.exprs {
            if let HdlExpr::Assign(..) = e {
                out.push_str(&emit_expr(e, 0, false));
                out.push('\n');
            }
        }
    }

    out.push_str("\nendmodule\n");
    out
}
