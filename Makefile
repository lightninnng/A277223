.PHONY: certs audit lean paper check clean

certs:
	python3 scripts/generate_carry_certificates.py

audit:
	python3 scripts/arithmetic_audit.py

lean:
	lake build

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

check: certs audit lean paper

clean:
	cd paper && latexmk -C main.tex
	rm -rf .lake/build
