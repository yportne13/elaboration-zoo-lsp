import os
os.chdir(r'F:\projects\hermes\elaboration-zoo-lsp')

with open('src/prelude/hdl/hdl-macros.typort', 'r') as f:
    content = f.read()

# Find the switch rules section
tag1 = '    // ---- switch control flow ----'
tag2 = '    // ---- assignment'

idx1 = content.find(tag1)
idx2 = content.find(tag2)

if idx1 >= 0 and idx2 > idx1:
    replacement = '''    // ---- switch — use function-based switchOnExpr instead ----
    // See hdl-ops.typort: switchOnExpr(sel.expr).isValueExpr(v.expr, { ... }).default({ ... })

    // ---- assignment'''
    content = content[:idx1] + replacement + content[idx2 + len('    // ---- assignment'):]
    with open('src/prelude/hdl/hdl-macros.typort', 'w') as f:
        f.write(content)
    print('Removed switch macro rules')
else:
    print(f'Not found: idx1={idx1}, idx2={idx2}')
    # Show what's at those positions
    lines = content.split('\n')
    for i, line in enumerate(lines):
        if 'switch' in line or 'assignment' in line:
            print(f'L{i+1}: {line}')
