/*
 Pour tester en supprimant le code C++
   java -cp .:../antlr-4.13.2-complete.jar org.antlr.v4.gui.TestRig test start -tree input.txt
*/

parser grammar ExprParser;

options { tokenVocab=ExprLexer; }

@header {
#include "Expr.h"
#include "tools.h"
#include <stdio.h>
#include <iostream>
}

start returns [ExprPtr node]: e=add_expr EOF { $node=$e.node; };


/* ******************************************************************************************************* */
/* ******************************************************************************************************* */
/* --------------------------------------- Scalar expressions -------------------------------------------- */
/* ******************************************************************************************************* */
/* ******************************************************************************************************* */

/* level 0 */
primary returns [ExprPtr node] :  
    /* INT */
       INT 
        { 
         $node = std::make_unique<IntNode>(std::stoi($INT.text)); 
         //std::cout << TypeNodeToString($node->type) << std::endl;
         //printf("%s", TypeNodeToString($node->getType()));
        }
    /* DOUBLE */
    | DOUBLE { 
              $node = std::make_unique<DoubleNode>(std::stold($DOUBLE.text));
             }
    
    /* DOUBLE Extended */
    | DOUBLEExt { 
                 $node = std::make_unique<DoubleNode>(std::stold($DOUBLEExt.text));
                }
    
    /* IDENT */
    | IDENT { 
             $node = std::make_unique<IdentNode>($IDENT.text[0]);
            }

    /* (add_expr) */
    |  LEFTPAR e=add_expr RIGHTPAR
       { 
        $node = $e.node; 
       }

    /* Euclidian Norm */
    /* Default 
        * Euclidian norm for vectors and 
        * Spectral Norm for matrices and 
        * absolute value for scalars */
    |  (BARRE | LEFTBARRE | LEFTNORM) norm=add_expr (BARRE | RIGHTBARRE | RIGHTNORM)
       { 

             if ($norm.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ 'Euclidian Norm' RULE" );

            $node = std::make_shared<UnaryOpNode>(
                    "EuclideanNorm",
                    $norm.node
                );
       }

    /* Frobenius Norm */
    |  LEFTNORM norm=add_expr RIGHTNORM UNDERSCORE IDENT
       { 
            if ($norm.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ 'Frobenius Norm' RULE" );

            if ($IDENT.text[0] == 'F' || $IDENT.text[0] == 'f')
                $node = std::make_shared<UnaryOpNode>(
                        "FrobeniusNorm",
                        $norm.node
                    );
            else
                throw std::invalid_argument( "ERROR = NORM WITH STRANGE ARGUMENTS !" );
       }

    /* Vector accesses */
    |  LEFTPAR sub=add_expr RIGHTPAR LEFTSQ indice=add_expr RIGHTSQ
       { 
            if ( ($sub.node == nullptr) || ($indice.node == nullptr))
                throw std::invalid_argument( "SYNTAX ERROR @ 'Vector accessess' RULE" );
            
            $node = std::make_shared<BinaryOpNode>(
                    "VectorAccess",
                    $sub.node,
                    $indice.node
                );
       }

    /* Vector accesses of ident */
    | IDENT LEFTSQ indiceI=add_expr RIGHTSQ
        {
            if ($indiceI.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ 'Vector accessess of ident' RULE" );

            $node = std::make_shared<BinaryOpNode>(
                    "VectorAccess",
                    std::make_unique<IdentNode>($IDENT.text[0]),
                    $indiceI.node
                );
        }
    
    /* Vector accesses of ident with subscribe */
    | vector=IDENT UNDERSCORE indiceVI=IDENT
        {
            $node = std::make_shared<BinaryOpNode>(
                    "VectorAccess",
                    std::make_unique<IdentNode>($vector.text[0]),
                    std::make_unique<IdentNode>($indiceVI.text[0])
                );
        }
    ;


/* level 1 */
unary_expr returns [ExprPtr node] @init{bool empty = true; int multiChoix1 = 0; int multiChoix2 = 0; }: 
    /* ***************** -prim ************** */
    (opS+=MINUS {empty = false;})? primS=primary 
        { 
            if ($primS.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ '-prim' RULE" );
            
            // if no unary_operator
            if (empty)
                    $node=$primS.node;
            else {
                 if (auto intNode = dynamic_cast<IntNode*>($primS.node.get()))
                    $node = std::make_unique<IntNode>(-intNode->value);
                 else
                 if (auto doubleNode = dynamic_cast<DoubleNode*>($primS.node.get()))
                    $node = std::make_unique<DoubleNode>(-doubleNode->value);
                    
                else
                    $node = std::make_shared<UnaryOpNode>("-",$primS.node);
            }
        }
    
    /* ***************** prim! or prim% *********** */
    |  sub=primary (op+=(FACT | PERCENT))+
        { 
            if ($sub.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ 'prim! or prim%' RULE" );
            
            $node = $sub.node;
            for (int i = 0; i < $op.size(); ++i) {
                $node = std::make_shared<UnaryOpNode>(
                    $op[i]->getText(),
                    $node
                );
            }
        }
    
    /* ***************** prim^a *********** */
    | sub=primary CIRCUMFLEX IDENT
      {
        if ($sub.node == nullptr)
            throw std::invalid_argument( "SYNTAX ERROR @ 'prim^a' RULE" );
        
        if ($IDENT.text[0] == 'T')
            $node = std::make_shared<UnaryOpNode>("Transpose",$sub.node);
        else
            $node = std::make_shared<BinaryOpNode>(
                    "^",
                    $sub.node,
                    std::make_unique<IdentNode>($IDENT.text[0])
                );
      }
    
    /* ***************** prim^2 *********** */
    | sub=primary CIRCUMFLEX INT
      {
        if ($sub.node == nullptr)
            throw std::invalid_argument( "SYNTAX ERROR @ 'prim^2' RULE" );

        int how = std::stoi($INT.text); 
        if (how > 9) {
            throw std::invalid_argument( "ERROR = POWER TO AN INTEGER > 9 !" );
        }
        $node = std::make_shared<BinaryOpNode>(
                    "^",
                    $sub.node,
                    std::make_unique<IntNode>(how)
                );
      }

    /* ***************** prim^{expr} *********** */
    | subDown=primary CIRCUMFLEX LEFTB subUp=add_expr RIGHTB
      {
        if (($subDown.node == nullptr) || ($subUp.node == nullptr))
            throw std::invalid_argument( "SYNTAX ERROR @ 'prim^{expr}' RULE" );
        
        if (auto intNode = dynamic_cast<IntNode*>($subUp.node.get()))
            if (intNode->value == -1)
                $node = std::make_shared<UnaryOpNode>(
                        "Inverse",
                        $subDown.node
                    );
            else 
                $node = std::make_shared<BinaryOpNode>(
                        "^",
                        $subDown.node,
                        $subUp.node
                    );
        else
        if (auto identNode = dynamic_cast<IdentNode*>($subUp.node.get()))
            if (identNode->value == 'T')
                $node = std::make_shared<UnaryOpNode>(
                        "Transpose",
                        $subDown.node
                    );
            else
                $node = std::make_shared<BinaryOpNode>(
                        "^",
                        $subDown.node,
                        $subUp.node
                    );
     }

    // TODO: tester que "f" est bien une fonction pour éviter le f*(e1,...,en)
    /* ***************** f or \fun (expr,...,expr) *********** */
    | (fun=IDENT {multiChoix1 = 1;} | fun=FUNCTION {multiChoix1 = 2;}) LEFTPAR (firstArg=add_expr (COMMA othersArg+=add_expr)* {empty = false;})? RIGHTPAR
      {
        if (($firstArg.node == nullptr) || (validateVector($othersArg)))
            throw std::invalid_argument( "SYNTAX ERROR @ 'f or \\fun (expr,...,expr)' RULE" );        
        
        // si pas d'arguments
        if (empty) {
            std::vector<ExprPtr> emptyVector;
            $node = std::make_shared<FunCallNode>(($fun.text),emptyVector);
        }
        else {
            std::vector<ExprPtr> args;
            args.push_back($firstArg.node);
            for (int i = 0; i < $othersArg.size(); ++i)
                args.push_back($othersArg[i]->node);
            $node = std::make_shared<FunCallNode>(($fun.text),args);
        }
      }

    // TODO: est-ce une règle bien utile ? Forcer \fun{args} ???
    /* \fun prim */
    | funcEmpty=FUNCTION subFUNC=primary
     {
        if ($subFUNC.node == nullptr)
            throw std::invalid_argument( "SYNTAX ERROR @ '\\fun prim' RULE" );

        std::vector<ExprPtr> args;
        args.push_back($subFUNC.node);
        $node = std::make_shared<FunCallNode>(($funcEmpty.text),args);
     }

    /* ***************** \sinus {expr}...{expr} *********** */
    // TODO: traiter autre cas que "dfrac/tfrac/frac" s'il y a ...
    /* \func{}{}...{} */
    | func=FUNCTION (LEFTB argFUNCT+=add_expr RIGHTB)+
      {
        if (validateVector($argFUNCT))
            throw std::invalid_argument( "SYNTAX ERROR @ '\\func{}{}...{}' RULE" );

        std::string op =  fromFunctionToOperation($argFUNCT.size(), $func.text);
        if (op!=" ") {
            $node =  std::make_shared<BinaryOpNode>(
                op,
                $argFUNCT[0]->node,
                $argFUNCT[1]->node
            );
        }
        else {
                std::vector<ExprPtr> args;
                for (int i = 0; i < $argFUNCT.size(); ++i)
                    args.push_back($argFUNCT[i]->node);
                $node = std::make_shared<FunCallNode>($func.text,args);
            }
      }

    /* | BigSUM UNDERSCORE LEFTB indice=IDENT EQUAL under=add_expr RIGHTB CIRCUMFLEX LEFTB over=add_expr RIGHTB subSum=add_expr
        {
            $node=std::make_shared<BigSumNode>(
                $indice.text[0],
                $under.node,
                $over.node,
                $subSum.node
            );
        }
    | BigSUM UNDERSCORE LEFTB indice=IDENT EQUAL under=add_expr RIGHTB CIRCUMFLEX overI=IDENT subSumI=add_expr
        {
            $node=std::make_shared<BigSumNode>(
                $indice.text[0],
                $under.node,
                std::make_unique<IdentNode>($overI.text[0]),
                $subSumI.node
            );
        }

    | BigSUM UNDERSCORE LEFTB indice=IDENT EQUAL under=add_expr RIGHTB CIRCUMFLEX INT subSumI=add_expr
        {
            int how = std::stoi($INT.text); 
            if (how > 9) {
                throw std::invalid_argument( "ERROR = SUM WITH OVER INTEGER > 9 !" );
            }
            $node=std::make_shared<BigSumNode>(
                $indice.text[0],
                $under.node,
                std::make_unique<IntNode>(how),
                $subSumI.node
            );
        }
*/

    /* BigSUM */
    | BigSUM UNDERSCORE LEFTB indice=IDENT EQUAL under=add_expr RIGHTB CIRCUMFLEX
            ( (LEFTB over=add_expr (COMMA cond=or_expr {empty = false;})? RIGHTB) {multiChoix1 = 1;} | overSumInt=INT {multiChoix1 = 2;}  | overSumI=IDENT {multiChoix1 = 3;} )
            subSum=add_expr
        {
            if (($under.node == nullptr) || ($subSum.node == nullptr))
                throw std::invalid_argument( "SYNTAX ERROR @ 'BigSUM' RULE" );
            
            ExprPtr over;

            switch (multiChoix1) {
                case 1: {
                    if ($over.node == nullptr)
                        throw std::invalid_argument( "SYNTAX ERROR @ 'BigSUM' RULE" );
                    over = $over.node; 
                    break;
                }
                case 2: {
                    int how = std::stoi($overSumInt.text); 
                    if (how > 9) { 
                        throw std::invalid_argument( "ERROR = INT WITH OVER INTEGER > 9 !" );
                    }
                    over = std::make_unique<IntNode>(how); 
                    break;
                    }
                case 3: {
                    over = std::make_unique<IdentNode>($overSumI.text[0]);
                    break;
                    }
                default: throw std::invalid_argument( "ERROR = SUM WITH STRANGE ARGUMENTS (OVER) !" );
            }

            $node=std::make_shared<BigSumNode>(
                $indice.text[0],
                $under.node,
                over,
                $subSum.node,
                empty ? nullptr : $cond.node
            );

        }


    // TODO: rajouter autre que Simpson, par exemple Trapeze, Gauss, etc.
        // https://www.bibmath.net/dico/index.php?action=affiche&quoi=./s/simpson_meth.html
        //\int_a^b f(t)dt \simeq \frac{h}{6}\sum_{k=0}^{n-1}\left(f\left(a+kh\right)+4f\left(a+(k+1/2)h\right)+f(a+(k+1)h)\right)
        // h=(b-a)/n

    // TODO correction avec http://serge.mehl.free.fr/anx/meth_simpson.html (et fichier PDF)

    // TODO intégrale multiples !!!!

    // https://fr.wikipedia.org/wiki/Int%C3%A9grale_multiple

    // https://www.youtube.com/watch?v=UNPOBuY-t_A


    /* INTEGRALE */
    | INTEGRALE UNDERSCORE ((LEFTB underInt=add_expr RIGHTB) {multiChoix1 = 1;} | underIntINT=INT {multiChoix1 = 2;} | underIntIDENT=IDENT {multiChoix1 = 3;}) 
                CIRCUMFLEX ((LEFTB overInt=add_expr RIGHTB)  {multiChoix2 = 1;} | overIntINT=INT  {multiChoix2 = 2;} | overIntIDENT=IDENT  {multiChoix2 = 3;})
                subINT=add_expr DERIVE LEFTB varInt=IDENT RIGHTB 
        {
            if ($subINT.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ 'INTEGRALE' RULE" );

            ExprPtr a;
            ExprPtr b;

            switch (multiChoix1) {
                case 1: {
                    if ($underInt.node == nullptr)
                        throw std::invalid_argument( "SYNTAX ERROR @ 'INTEGRALE' RULE" );
                     a = $underInt.node;
                     break;
                    }
                case 2: {
                    int how = std::stoi($underIntINT.text); 
                    if (how > 9) { 
                        throw std::invalid_argument( "ERROR = INT WITH UNDER INTEGER > 9 !" );
                    }
                    a = std::make_unique<IntNode>(how); 
                    break;
                    }
                case 3: {
                    a = std::make_unique<IdentNode>($underIntIDENT.text[0]);
                    break;
                    }
                default: throw std::invalid_argument( "ERROR = INTEGRALE WITH STRANGE ARGUMENTS (UNDER) !" );
            }

            switch (multiChoix2) {
                case 1: { 
                    if ($overInt.node == nullptr)
                        throw std::invalid_argument( "SYNTAX ERROR @ 'INTEGRALE' RULE" );
                    b = $overInt.node; 
                    break;
                    }
                case 2: {
                    int how = std::stoi($overIntINT.text); 
                    if (how > 9) { 
                        throw std::invalid_argument( "ERROR = INT WITH OVER INTEGER > 9 !" );
                    }
                    b = std::make_unique<IntNode>(how); 
                    break;
                    }
                case 3: {
                    b = std::make_unique<IdentNode>($overIntIDENT.text[0]);
                    break;
                    }
                default: throw std::invalid_argument( "ERROR = INTEGRALE WITH STRANGE ARGUMENTS (OVER) !" );
            }


            ExprPtr h = std::make_shared<BinaryOpNode>(
                "/",
                std::make_shared<BinaryOpNode>("-",
                    a,
                    b
                ),
                std::make_shared<IdentNode>('N')
            );

            $node = std::make_shared<BinaryOpNode>(
                    "*",
                    std::make_shared<BinaryOpNode>(
                        "/",
                        h,
                        std::make_shared<DoubleNode>(6.0)
                    ),
                   std::make_shared<BigSumNode>(
                        'k',
                        std::make_shared<IntNode>(0),
                        std::make_shared<BinaryOpNode>(
                           "-",
                            std::make_shared<IdentNode>('N'),
                            std::make_shared<IntNode>(1)
                        ),
                        std::make_shared<BinaryOpNode>(
                            "+",
                            substitute(
                                $subINT.node, 
                                $varInt.text[0], 
                                std::make_shared<BinaryOpNode>(
                                    "+",
                                    std::make_shared<IdentNode>('a'),
                                    std::make_shared<BinaryOpNode>(
                                        "*",
                                        std::make_shared<IdentNode>('k'),
                                        h
                                    )
                                )
                            ),
                            std::make_shared<BinaryOpNode>(
                                "+",
                                std::make_shared<BinaryOpNode>(
                                    "*",
                                    std::make_shared<DoubleNode>(4.0),
                                    substitute(
                                        $subINT.node, 
                                        $varInt.text[0], 
                                        std::make_shared<BinaryOpNode>(
                                            "+",
                                            std::make_shared<IdentNode>('a'),
                                            std::make_shared<BinaryOpNode>(
                                                "*",
                                                std::make_shared<BinaryOpNode>(
                                                    "+",
                                                    std::make_shared<IdentNode>('k'),
                                                    std::make_shared<DoubleNode>(0.5)
                                                ),
                                                h
                                            )
                                        )
                                    )
                                ),
                                substitute(
                                    $subINT.node, 
                                    $varInt.text[0], 
                                    std::make_shared<BinaryOpNode>(
                                        "+",
                                        std::make_shared<IdentNode>('a'),
                                        std::make_shared<BinaryOpNode>(
                                            "*",
                                            std::make_shared<BinaryOpNode>(
                                                "+",
                                                std::make_shared<IdentNode>('k'),
                                                std::make_shared<DoubleNode>(1)
                                            ),
                                            h
                                        )
                                    )
                                )
                            )
                        )
                    )
                );
        }
    ;

/* level 2 */
mult_expr returns [ExprPtr node]:
    // TODO: vérifier si ce IMUL ne gene pas, il vient a cause des \sum_{i=0}^n x  car l'outil ajoute un IMUL entre "n" et "x" comme un idiot...
    /* MULT */
   (IMUL)? sub=unary_expr (op+=(MUL | SLASH | IMUL) mult+=unary_expr)*
        {
            if (($sub.node == nullptr) || (validateVector($mult)))
                throw std::invalid_argument( "SYNTAX ERROR @ 'MULT' RULE" );

            $node = $sub.node;
            for (int i = 0; i < $op.size(); ++i) {
                // si la longueur du texte est > 1 c'est que MUL=\times
                if ($op[i]->getText().length()>1)
                    $node = std::make_shared<BinaryOpNode>(
                        "*",
                        $node,
                        $mult[i]->node
                );
                else
                    $node = std::make_shared<BinaryOpNode>(
                        $op[i]->getText(),
                        $node,
                        $mult[i]->node
                    );
            }
        }
        ;

/* level 3 */
add_expr returns [ExprPtr node]:
    /* ADD */
    sub=mult_expr (op+=(ADD | MINUS) sum+=mult_expr)*
        {
            if (($sub.node == nullptr) || (validateVector($sum)))
                throw std::invalid_argument( "SYNTAX ERROR @ 'ADD' RULE" );
            
            $node = $sub.node;
            for (int i = 0; i < $op.size(); ++i) {
                $node = std::make_shared<BinaryOpNode>(
                    $op[i]->getText(),
                    $node,
                    $sum[i]->node
                );
            }
        }
    ;



/* ******************************************************************************************************* */
/* ******************************************************************************************************* */
/* --------------------------------------- Boolean expressions ------------------------------------------- */
/* ******************************************************************************************************* */
/* ******************************************************************************************************* */

// TODO : bien vérifier l'ordre des niveaux, car AND est ici prioritaire sur OR

/* level 0 */
primary_bool returns [ExprPtr node] :    
       FALSE { 
             $node = std::make_unique<BoolNode>(false);
            }
    | TRUE  { 
             $node = std::make_unique<BoolNode>(true);
            }
    | IDENT { 
             $node = std::make_unique<IdentNode>($IDENT.text[0]);
            }

    |  LEFTPAR e=or_expr RIGHTPAR
       { 
        $node = $e.node; 
       }
    
    | primLeft=unary_expr (op+=(EQUAL | LESS | GREATER | NotEQUAL | LESSOREQUAL | GREATEROREQUAL) primRight=unary_expr)
        {
            $node = std::make_shared<BinaryOpNode>(
                $op[0]->getText(),
                $primLeft.node,
                $primRight.node
            );
        }
    ;

/* level 1 */
unary_bool returns [ExprPtr node] @init{bool empty = true;}: 
    /* ***************** \neg prim ************** */
    (opS+=BoolNOT {empty = false;})? primS=primary_bool 
        { 
            if ($primS.node == nullptr)
                throw std::invalid_argument( "SYNTAX ERROR @ '\\neg prim' RULE" );
            
            // if no unary_operator
            if (empty)
                    $node=$primS.node;
            else 
                $node = std::make_shared<UnaryOpNode>("NOT",$primS.node);
        }
    ;

/* level 2 */
and_expr returns [ExprPtr node]:
    /* AND */
    sub=unary_bool (op+=BoolAND sum+=unary_bool)*
        {
            if (($sub.node == nullptr) || (validateVector($sum)))
                throw std::invalid_argument( "SYNTAX ERROR @ 'AND' RULE" );
          
            $node = $sub.node;
            for (int i = 0; i < $op.size(); ++i) {
                $node = std::make_shared<BinaryOpNode>(
                    "AND",
                    $node,
                    $sum[i]->node
                );
            }
        }
    ;

/* level 3 */
or_expr returns [ExprPtr node]:
    /* OR */
    sub=and_expr (op+=BoolOR sum+=and_expr)*
        {
            if (($sub.node == nullptr) || (validateVector($sum)))
                throw std::invalid_argument( "SYNTAX ERROR @ 'OR' RULE" );
         
            $node = $sub.node;
            for (int i = 0; i < $op.size(); ++i) {
                $node = std::make_shared<BinaryOpNode>(
                    "OR",
                    $node,
                    $sum[i]->node
                );
            }
        }
    ;


/* ******************************************************************************************************* */
/* ******************************************************************************************************* */
/* --------------------------------------- Vector/Matrices ----------------------------------------------- */
/* ******************************************************************************************************* */
/* ******************************************************************************************************* */


/* ******************************************************************************************************* */
/* ******************************************************************************************************* */
/* --------------------------------------- Case expressions ---------------------------------------------- */
/* ******************************************************************************************************* */
/* ******************************************************************************************************* */


/* ******************************************************************************************************* */
/* ******************************************************************************************************* */
/* --------------------------------------- Temporal expressions ------------------------------------------ */
/* ******************************************************************************************************* */
/* ******************************************************************************************************* */