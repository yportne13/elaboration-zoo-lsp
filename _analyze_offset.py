import sys
content = open('src/prelude/hdl/hdl-core.typort', 'r').read()
print('File length:', len(content))
start = max(0, 4080 - 50)
end = min(len(content), 4080 + 200)
print('Context around 4080:')
print(repr(content[start:end]))
print('---')
lines = content[:4080].split('\n')
print('Line number for offset 4080:', len(lines))
content_lines = content.split('\n')
for i in range(len(lines)-3, min(len(content_lines), len(lines)+10)):
    print(i+1, ':', content_lines[i] if i < len(content_lines) else 'EOF')
sys.stdout.flush()
