#!/usr/bin/env python3
"""One-off: convert round-8 regex expectations to plain substring matching."""
import io, re

p = 'tools/review-1011/gen_r08.py'
s = io.open(p, encoding='utf-8').read()

# Replace every "stdout /<regex>/" expectation with a substring form by
# stripping the /.../ wrapper and unescaping regex escapes to literals.
def conv(m):
    pat = m.group(1)
    # unescape common regex metas used in the corpus to their literal forms
    pat = pat.replace('\\(', '(').replace('\\)', ')').replace('\\+', '+')
    pat = pat.replace('\\*', '*').replace('\\[', '[').replace('\\]', ']')
    pat = pat.replace('\\?', '?').replace('\\|', '|').replace('\\{', '{')
    pat = pat.replace('\\}', '}')
    return f'"stdout {pat}"'

s2 = re.sub(r'"stdout /((?:[^/\\]|\\.)*)/"', conv, s)
io.open(p, 'w', encoding='utf-8', newline='\n').write(s2)
n1 = len(re.findall(r'"stdout /', s))
n2 = len(re.findall(r'"stdout /', s2))
print('remaining regex expects:', n2)
import ast
ast.parse(s2)
print('syntax ok')
