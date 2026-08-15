import re
p = r'F:\projects\hermes\elaboration-zoo-lsp\tests\probe_macro_bugs.rs'
src = open(p, encoding='utf-8').read()
s = re.sub(r'"(?:[^"\\]|\\.)*"', '""', src)
s = re.sub(r'//[^\n]*', '', s)
depth = 0
line = 1
events = []
for ch in s:
    if ch == '\n':
        line += 1
    elif ch == '{':
        depth += 1
        events.append((line, depth))
    elif ch == '}':
        depth -= 1
        events.append((line, depth))
print('final depth:', depth)
# Show events from line 150 onward
for ln, d in events:
    if ln >= 150:
        print(ln, d)
