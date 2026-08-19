# Manuscript

`main.tex` contains the self-contained mathematical proof. Build it with

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The proof has four layers:

1. Carry Obstruction excludes maximal values `1,2,3,4,5,6,8,10`.
2. Periodic Crossing proves the explicit `7` and `11` constructions and their parameterized infinite families.
3. Elementary witnesses realize `0` and `9`.
4. The final theorem gives the exact spectrum below `12`.

The final appendix maps the principal mathematical statements to the supplementary Lean declarations. Formal verification details and the CI trust boundary are documented in `../VERIFICATION.md`.
