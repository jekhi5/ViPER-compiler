test: expr.ml sexp.ml test.ml
	ocamlfind ocamlc -o test -package extlib,ounit2,str -linkpkg -g expr.ml sexp.ml test.ml

clean:
	rm -f test *.log *.cmi *.cmo *.cache
