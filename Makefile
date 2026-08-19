.PHONY: certs checks lean paper verify clean

certs:
	python3 scripts/generate_carry_certificates.py

checks: certs
	python3 scripts/arithmetic_audit.py
	python3 scripts/infinite_family_audit.py
	python3 scripts/static_lean_audit.py

lean:
	lake build

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

verify: checks lean

clean:
	cd paper && latexmk -C main.tex
	rm -rf .lake/build
