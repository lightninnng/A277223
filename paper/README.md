# Manuscript

`main.tex` is the paper source. Build with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The paper follows the same dependency graph as the Lean development:

1. **Carry Obstruction** excludes maximal values `1,2,3,4,5,6,8,10`.
2. **Periodic Crossing** proves that the explicit periodic witnesses have unique positive Good multipliers `7` and `11`.
3. Elementary witnesses realize `0` and `9`.
4. The final theorem gives the exact spectrum below `12`.

The generated repository snapshot may be mathematically complete while still awaiting an actual `lake build`; see `../FORMALIZATION_STATUS.md` before making a machine-checked certification claim.
