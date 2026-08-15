clean:
	rm -f *.interp  ExprLexer.cpp  ExprLexer.h  *.interp  *.tokens  ExprParser.cpp  ExprParser.h

all:
	java -jar ../antlr-4.13.2-complete.jar -no-listener -no-visitor -encoding UTF-8 -Dlanguage=Cpp ExprLexer.g4
	java -jar ../antlr-4.13.2-complete.jar -no-listener -no-visitor -encoding UTF-8 -Dlanguage=Cpp ExprParser.g4
	g++ -std=c++23 VectorTokenSource.cpp tools.cpp Expr*.cpp main.cpp -lantlr4-runtime -I /usr/local/include/antlr4-runtime -o parser

parser:
	g++ -std=c++23 VectorTokenSource.cpp tools.cpp Expr*.cpp main.cpp -lantlr4-runtime -I /usr/local/include/antlr4-runtime -o parser

run:
	./parser input.tex