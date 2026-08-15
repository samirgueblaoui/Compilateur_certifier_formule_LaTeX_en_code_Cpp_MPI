/* ************************************ */
/* ************************************ */
/*  ************ LEXER **************** */
/* ************************************ */
/* ************************************ */

lexer grammar ExprLexer;

// For implicit multiplication, we will insert an IMUL token between certain pairs of tokens
// For example, between a NUMBER and a VARIABLE, or between a VARIABLE and a LEFTPAR
// We will handle this in C++ code by looking at the previous token and the next token to decide when to insert an IMUL token for each reading token.
tokens { IMUL }

/* Skip whitespaces, tabs, newlines and some special commands in LaTeX  */
WS      : [ \t\r\n]+ -> skip;
IGNORE_SPACE_COMMAND : BACKSLASH ('quad' | 'qquad' | ',' | '!' | ' ' | 'limits' | 'nolimits') -> skip;
LINE_COMMENT: '%' ~[\r\n]* -> skip;


/* SUM */
BigSUM    : BACKSLASH 'sum';
INTEGRALE : BACKSLASH 'int';
DERIVE    : BACKSLASH 'derive';



/* ************* INT & Double *********** */
INT     : DIGIT+ ;
DOUBLE  : DIGIT+ '.' DIGIT*
        | '.' DIGIT+
        ;
DOUBLEExt : DOUBLE [eE] [-+]? DIGIT+ ;
DIGIT   : [0-9];


/* ************* operators  *********** */
MUL        : '*' | BACKSLASH 'times';
ADD        : '+';
MINUS      : '-';
FACT       : '!';
PERCENT    : '\\%';
CIRCUMFLEX : '^';
SLASH      : '/';
EQUAL          : '=' | BACKSLASH 'eq';
LESS           : '<' | BACKSLASH 'lt';
GREATER        : '>' | BACKSLASH 'gt';
NotEQUAL       : BACKSLASH 'neq' | BACKSLASH 'ne';
LESSOREQUAL    : BACKSLASH 'leq' | BACKSLASH 'le';
GREATEROREQUAL : BACKSLASH 'geq' | BACKSLASH 'ge';


/* *************** constructors ******** */
LEFTPAR    : '(' | BACKSLASH 'left(';
RIGHTPAR   : ')' | BACKSLASH 'right)';
BACKSLASH  : '\\';
AMPERSAND  : '&';
LEFTB      : '{';
RIGHTB     : '}';
LEFTSQ     : '[';
RIGHTSQ    : ']';
UNDERSCORE : '_';
COMMA      : ',';
BARRE      : '|';
LEFTBARRE  : BACKSLASH 'left|'  | BACKSLASH 'lvert';
RIGHTBARRE : BACKSLASH 'right|' | BACKSLASH 'rvert';
LEFTNORM   : BACKSLASH 'lVert';
RIGHTNORM  : BACKSLASH 'rVert';


/* ***************** booleans ******** */
FALSE     : BACKSLASH 'perp' | BACKSLASH 'bot';
TRUE      : BACKSLASH 'top';
BoolAND   : BACKSLASH 'wedge' | BACKSLASH 'land';
BoolOR    : BACKSLASH 'vee'   | BACKSLASH 'lor';
BoolNOT   : BACKSLASH 'lnot'  | BACKSLASH 'neg';


/* ************* literals *********** */
IDENT    : LETTER;
FUNCTION : BACKSLASH LETTER+;
LETTER   : [a-zA-Z];

/* 
 TODO: pour faire reconnaitre les lettres grecques en tant qu'identidiant il faut lire le fichier config.json, avoir cette liste de lettres grecques
puis avoir un lexer du genre:

IDENT : LETTER | BACKSLASH LETTER+ {isLetter(getText())}? ;
FUNCTION : BACKSLASH LETTER+;


import java.util.Set;
import java.util.HashSet;
import java.io.BufferedReader;
import java.io.FileReader;

public class FunctionHelper {
    private static Set<String> functions = new HashSet<>();

    static {
        try (BufferedReader br = new BufferedReader(new FileReader("functions.txt"))) {
            String line;
            while ((line = br.readLine()) != null) {
                functions.add(line.trim());
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public static boolean isFunction(String text) {
        return functions.contains(text);
    }
}


*/
