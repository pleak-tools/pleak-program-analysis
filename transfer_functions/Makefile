all: transfer_functions_intervals transfer_functions

transfer_functions_intervals: transfer_functions_intervals.ml syntax.mli myparser.mli lexer.ml
	ocamlopt -cc "g++" -I /usr/lib/ocaml/apron -o transfer_functions_intervals \
		/usr/lib/ocaml/bigarray.cmxa \
		/usr/lib/ocaml/apron/gmp.cmxa \
		/usr/lib/ocaml/apron/apron.cmxa \
		/usr/lib/ocaml/apron/boxMPQ.cmxa \
		syntax.mli \
		myparser.mli \
		myparser.ml \
		lexer.ml \
		transfer_functions_intervals.ml

myparser.mli: myparser.mly
	ocamlyacc myparser.mly

lexer.ml: lexer.mll
	ocamllex lexer.mll

transfer_functions: transfer_functions.ml
	ocamlopt -cc "g++" -I /usr/lib/ocaml/apron -o transfer_functions \
		/usr/lib/ocaml/bigarray.cmxa \
		/usr/lib/ocaml/apron/gmp.cmxa \
		/usr/lib/ocaml/apron/apron.cmxa \
		/usr/lib/ocaml/apron/polka.cmxa \
		transfer_functions.ml
