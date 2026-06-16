import os
os.chdir(r'F:\projects\hermes\elaboration-zoo-lsp')

with open('src/prelude/hdl/hdl-macros.typort', 'r') as f:
    lines = f.readlines()

# Remove switch / is / default section (lines 88-101)
result = []
skip = False
for line in lines:
    if '// ---- switch / is / default' in line:
        skip = True
        continue
    if skip and '// ---- raw expression passthrough' in line:
        skip = False
        result.append(line)
        continue
    if not skip:
        result.append(line)

with open('src/prelude/hdl/hdl-macros.typort', 'w') as f:
    f.writelines(result)

print('Removed old switch rules')
