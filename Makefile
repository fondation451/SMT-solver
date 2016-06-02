all: smt main
	ocamlc -annot -g -o smt_solver persistent_array.cmo persistent_union_find.cmo ast.cmo smt.cmo lexer.cmo parser.cmo main.cmo

main: smt parser_compil parser_inter lexer_compil
	ocamlc -annot -g -c main.ml

lexer:
	ocamllex lexer.mll

parser:
	menhir --infer --explain -v parser.mly
	
parser_compil: parser parser_inter
	ocamlc -annot -g -c parser.ml

parser_inter: parser
	ocamlc -annot -g -c parser.mli
	
lexer_compil: lexer
	ocamlc -annot -g -c lexer.ml

ast:
	ocamlc -annot -g -c ast.ml

array:
	ocamlc -annot -g -c persistent_array.ml

union: array
	ocamlc -annot -g -c persistent_union_find.ml

theory: union
	ocamlc -annot -g persistent_array.cmo persistent_union_find.cmo theory_sat.ml

smt: union ast
	ocamlc -annot -g -c smt.ml

clean:
	rm -f *.cm[io] *.o *.annot *~ smt_solver lexer.ml parser.ml cparser.mli
	rm -f *.output *.automaton *.conflicts


































