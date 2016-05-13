main.ml: ast.ml parser.mli parser.ml lexer.ml persistent_array.ml persistent_union_find.ml equality_theory_solver.ml smt.ml
	ocamlc ast.ml parser.mli parser.ml lexer.ml persistent_array.ml persistent_union_find.ml equality_theory_solver.ml smt.ml main.ml

lexer.ml: lexer.mll
	ocamllex lexer.mll

parser.ml parser.mli: parser.mly
	menhir parser.mly

clean:
	rm *.cmi *.cmo
	rm parser.mli parser.ml lexer.ml
	rm a.out
