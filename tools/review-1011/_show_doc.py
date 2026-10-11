#!/usr/bin/env python3
t = open('docs/typeclass-syntax.md', encoding='utf-8').read()
key = '4. ' + chr(38544) + chr(24335)  # section 4 keyword
i = t.find('## ' + key)
if i < 0:
    i = t.find(key)
print(t[i:i + 2000])
