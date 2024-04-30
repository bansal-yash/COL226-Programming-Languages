run:
	ocamlc -c Types.ml
	ocamllex lexer.mll
	ocamlyacc -v parser.mly
	ocamlc -c parser.mli
	ocamlc -c lexer.ml
	ocamlc -c parser.ml
	ocamlc -c main.ml
	ocamlc -o main Types.cmo parser.cmo lexer.cmo main.cmo 
	./main input.pl
	rm Types.cmi Types.cmo parser.output lexer.cmi lexer.cmo lexer.ml main main.cmi main.cmo parser.cmi parser.cmo parser.ml parser.mli
	
clean: