run:
	ocamlc -c -warn-error +a Types.ml
	ocamlyacc -v parser.mly
	ocamlc -c -warn-error +a parser.mli
	ocamlc -c -warn-error +a parser.ml
	ocamllex lexer.mll
	ocamlc -c -warn-error +a lexer.ml
	ocamlc -c -warn-error +a main.ml

	ocamlc -o main Types.cmo parser.cmo lexer.cmo main.cmo 
	./main input.pl goal.pl
	rm parser.output lexer.cmo lexer.ml main main.cmi main.cmo parser.cmo parser.ml parser.mli Types.cmo
	
clean:
	rm parser.output lexer.cmo lexer.ml main main.cmi main.cmo parser.cmo parser.ml parser.mli Types.cmo
