/// Test the position_to_offset and offset_to_position functions with Chinese characters
use ropey::Rope;
use lsp_types::Position;

use elaboration_zoo_lsp::{position_to_offset, offset_to_position};

#[test]
fn test_position_to_offset_ascii() {
    let rope = Rope::from_str("module foo;");
    // Positions in UTF-16 code units (same as byte offset for ASCII)
    assert_eq!(position_to_offset(Position::new(0, 0), &rope), Some(0));
    assert_eq!(position_to_offset(Position::new(0, 7), &rope), Some(7)); // ' ' at byte 7
    assert_eq!(position_to_offset(Position::new(0, 10), &rope), Some(10)); // ';' at byte 10
    assert_eq!(position_to_offset(Position::new(0, 11), &rope), Some(11)); // past end
}

#[test]
fn test_position_to_offset_chinese() {
    let rope = Rope::from_str("module 变量;");
    // UTF-16 code units: m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7) 量(8) ;(9)
    // Byte offsets:       m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7,8,9) 量(10,11,12) ;(13)

    // Position (0, 7) = '变' (1 UTF-16 code unit)
    assert_eq!(position_to_offset(Position::new(0, 7), &rope), Some(7));
    // Position (0, 8) = '量' (1 UTF-16 code unit, at byte 10)
    assert_eq!(position_to_offset(Position::new(0, 8), &rope), Some(10));
    // Position (0, 9) = ';' (1 UTF-16 code unit, at byte 13)
    assert_eq!(position_to_offset(Position::new(0, 9), &rope), Some(13));
    // Position (0, 0) = start
    assert_eq!(position_to_offset(Position::new(0, 0), &rope), Some(0));
}

#[test]
fn test_offset_to_position_chinese() {
    let rope = Rope::from_str("module 变量;");
    // Byte offsets: 0=m ... 6=' '  7=变 8=变 9=变  10=量 11=量 12=量  13=;

    // Byte offset 7 = start of '变' → Position (0, 7)
    assert_eq!(offset_to_position(7, &rope), Some(Position::new(0, 7)));
    // Byte offset 10 = start of '量' → Position (0, 8)
    assert_eq!(offset_to_position(10, &rope), Some(Position::new(0, 8)));
    // Byte offset 13 = ';' → Position (0, 9)
    assert_eq!(offset_to_position(13, &rope), Some(Position::new(0, 9)));
}

#[test]
fn test_incremental_edit_ascii() {
    // Simulate: buffer = "module foo;"
    // Editor sends: range start=char 7, end=char 10, text="bar"
    // This replaces "foo" (chars 7,8,9) with "bar", giving "module bar;"
    let mut rope = Rope::from_str("module foo;");
    let start_byte = position_to_offset(Position::new(0, 7), &rope).unwrap();
    let end_byte = position_to_offset(Position::new(0, 10), &rope).unwrap();
    // Convert byte offsets to char offsets (the fix for non-ASCII)
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "bar");
    assert_eq!(rope.to_string(), "module bar;");
}

#[test]
fn test_incremental_edit_chinese() {
    // Simulate: buffer = "module 变量;"
    // Editor sends: range start=char 9, end=char 9, text="测试"  (insert after 变量)
    // Expected: "module 变量测试;"
    let mut rope = Rope::from_str("module 变量;");
    let start_byte = position_to_offset(Position::new(0, 9), &rope).unwrap(); // byte 13 = ';'
    let end_byte = position_to_offset(Position::new(0, 9), &rope).unwrap();
    // Convert byte offsets to char offsets (the FIX)
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "测试");
    assert_eq!(rope.to_string(), "module 变量测试;");

    // Now replace "变量测试" with "你好"
    // After insert, string is "module 变量测试;" which is:
    // m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7) 量(8) 测(9) 试(10) ;(11)  [char indices]
    // m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7,8,9) 量(10,11,12) 测(13,14,15) 试(16,17,18) ;(19)  [byte indices]
    let start_byte = position_to_offset(Position::new(0, 7), &rope).unwrap(); // '变'
    let end_byte = position_to_offset(Position::new(0, 11), &rope).unwrap(); // after '试'
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "你好");
    assert_eq!(rope.to_string(), "module 你好;");
}

#[test]
fn test_roundtrip_conversion() {
    let texts = vec![
        "module simple;",
        "module 变量;",
        "module 变量测试;",
        " 空格 测试 123",
        "let x = 你好世界;",
        "type 布尔 = True | False; // 中文注释",
    ];

    for text in texts {
        let rope = Rope::from_str(text);
        for line in 0..rope.len_lines() {
            let line_text = rope.line(line);
            let mut utf16_pos = 0u32;
            // Test each character boundary
            for ch in line_text.chars() {
                let offset = position_to_offset(Position::new(line as u32, utf16_pos), &rope).unwrap();
                // Verify the offset points to the start of this character
                let line_start = rope.try_line_to_byte(line).unwrap();
                assert_eq!(offset, line_start + line_text.chars().take(utf16_pos as usize).map(|c| c.len_utf8()).sum::<usize>(),
                    "Failed for text {:?}, line {}, char {}", text, line, utf16_pos);

                // Round-trip: position → offset → position
                let pos_back = offset_to_position(offset, &rope).unwrap();
                assert_eq!(pos_back, Position::new(line as u32, utf16_pos),
                    "Round-trip failed for text {:?}, line {}, char {}", text, line, utf16_pos);

                utf16_pos += ch.len_utf16() as u32;
            }

            // Test end-of-line position
            let eol_offset = position_to_offset(Position::new(line as u32, utf16_pos), &rope).unwrap();
            let eol_pos = offset_to_position(eol_offset, &rope).unwrap();
            assert_eq!(eol_pos, Position::new(line as u32, utf16_pos),
                "EOL round-trip failed for text {:?}, line {}", text, line);
        }
    }
}

#[test]
fn test_rope_remove_insert_chinese() {
    // Simulate the did_change flow with byte→char conversion
    let mut rope = Rope::from_str("module a;// 你好世界");

    // Delete "a" and insert "变量"
    // "a" is at UTF-16 position 7, byte 7
    // After "a" is at UTF-16 position 8, byte 8
    let start_byte = position_to_offset(Position::new(0, 7), &rope).unwrap();
    let end_byte = position_to_offset(Position::new(0, 8), &rope).unwrap();
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "变量");

    // Expected: "module 变量;// 你好世界"
    assert_eq!(rope.to_string(), "module 变量;// 你好世界");
}

#[test]
fn test_did_change_simulation() {
    // Simulate the exact did_change flow:
    // buffer = "module 变量;"
    // Editor sends: range start=char 9, end=char 9, text="测试"
    let buffer = "module 变量;".to_string();
    let rope = Rope::from_str(&buffer);
    let start_byte = position_to_offset(Position::new(0, 9), &rope).unwrap();
    let end_byte = position_to_offset(Position::new(0, 9), &rope).unwrap();
    let mut rope = rope;
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "测试");
    let result = rope.to_string();
    assert_eq!(result, "module 变量测试;");
}

#[test]
fn test_character_past_line_end_clamps_to_line_content() {
    // character 超出**行内容**长度必须收敛到行末（终止符之前），不得滑进
    // 换行符乃至下一行行首（LSP 规范语义；旧实现 character=行内容长+1 时
    // 会落到 '\n' 上、+2 落到下一行行首）。
    let rope = Rope::from_str("ab\nline1\n");
    // 行 0 内容 "ab"（byte 0..2）：character=2 → '\n' 处；再大也仍是 byte 2
    assert_eq!(position_to_offset(Position::new(0, 2), &rope), Some(2));
    assert_eq!(position_to_offset(Position::new(0, 3), &rope), Some(2));
    assert_eq!(position_to_offset(Position::new(0, 99), &rope), Some(2));
    // 行 1 起点 byte 3，内容 "line1"：character=9 → clamp 到 byte 8
    assert_eq!(position_to_offset(Position::new(1, 9), &rope), Some(8));
    // 空行：任何 character 都收敛到行首
    let rope2 = Rope::from_str("a\n\nb");
    assert_eq!(position_to_offset(Position::new(1, 0), &rope2), Some(2));
    assert_eq!(position_to_offset(Position::new(1, 5), &rope2), Some(2));
}

#[test]
fn test_character_past_line_end_crlf_never_splits_terminator() {
    // CRLF：clamp 点在 '\r' 之前——绝不会落在 \r 与 \n 中间拆散终止符
    let rope = Rope::from_str("ab\r\nline1\r\n");
    // 行 0：内容 "ab"，'\r' 在 byte 2，clamp 后任何超长 character 都到 byte 2
    assert_eq!(position_to_offset(Position::new(0, 2), &rope), Some(2));
    assert_eq!(position_to_offset(Position::new(0, 3), &rope), Some(2));
    assert_eq!(position_to_offset(Position::new(0, 99), &rope), Some(2));
    // 行 1：起点 byte 4，内容 "line1"，'\r' 在 byte 9
    assert_eq!(position_to_offset(Position::new(1, 9), &rope), Some(9));
    assert_eq!(position_to_offset(Position::new(1, 10), &rope), Some(9));
}
