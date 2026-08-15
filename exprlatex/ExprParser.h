
#include "Expr.h"
#include "tools.h"
#include <stdio.h>
#include <iostream>


// Generated from ExprParser.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExprParser : public antlr4::Parser {
public:
  enum {
    IMUL = 1, WS = 2, IGNORE_SPACE_COMMAND = 3, LINE_COMMENT = 4, BigSUM = 5, 
    INTEGRALE = 6, DERIVE = 7, INT = 8, DOUBLE = 9, DOUBLEExt = 10, DIGIT = 11, 
    MUL = 12, ADD = 13, MINUS = 14, FACT = 15, PERCENT = 16, CIRCUMFLEX = 17, 
    SLASH = 18, EQUAL = 19, LESS = 20, GREATER = 21, NotEQUAL = 22, LESSOREQUAL = 23, 
    GREATEROREQUAL = 24, LEFTPAR = 25, RIGHTPAR = 26, BACKSLASH = 27, AMPERSAND = 28, 
    LEFTB = 29, RIGHTB = 30, LEFTSQ = 31, RIGHTSQ = 32, UNDERSCORE = 33, 
    COMMA = 34, BARRE = 35, LEFTBARRE = 36, RIGHTBARRE = 37, LEFTNORM = 38, 
    RIGHTNORM = 39, FALSE = 40, TRUE = 41, BoolAND = 42, BoolOR = 43, BoolNOT = 44, 
    IDENT = 45, FUNCTION = 46, LETTER = 47
  };

  enum {
    RuleStart = 0, RulePrimary = 1, RuleUnary_expr = 2, RuleMult_expr = 3, 
    RuleAdd_expr = 4, RulePrimary_bool = 5, RuleUnary_bool = 6, RuleAnd_expr = 7, 
    RuleOr_expr = 8
  };

  explicit ExprParser(antlr4::TokenStream *input);

  ExprParser(antlr4::TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options);

  ~ExprParser() override;

  std::string getGrammarFileName() const override;

  const antlr4::atn::ATN& getATN() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;


  class StartContext;
  class PrimaryContext;
  class Unary_exprContext;
  class Mult_exprContext;
  class Add_exprContext;
  class Primary_boolContext;
  class Unary_boolContext;
  class And_exprContext;
  class Or_exprContext; 

  class  StartContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    ExprParser::Add_exprContext *e = nullptr;
    StartContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EOF();
    Add_exprContext *add_expr();

   
  };

  StartContext* start();

  class  PrimaryContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    antlr4::Token *intToken = nullptr;
    antlr4::Token *doubleToken = nullptr;
    antlr4::Token *doubleextToken = nullptr;
    antlr4::Token *identToken = nullptr;
    ExprParser::Add_exprContext *e = nullptr;
    ExprParser::Add_exprContext *norm = nullptr;
    ExprParser::Add_exprContext *sub = nullptr;
    ExprParser::Add_exprContext *indice = nullptr;
    ExprParser::Add_exprContext *indiceI = nullptr;
    antlr4::Token *vector = nullptr;
    antlr4::Token *indiceVI = nullptr;
    PrimaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INT();
    antlr4::tree::TerminalNode *DOUBLE();
    antlr4::tree::TerminalNode *DOUBLEExt();
    std::vector<antlr4::tree::TerminalNode *> IDENT();
    antlr4::tree::TerminalNode* IDENT(size_t i);
    antlr4::tree::TerminalNode *LEFTPAR();
    antlr4::tree::TerminalNode *RIGHTPAR();
    std::vector<Add_exprContext *> add_expr();
    Add_exprContext* add_expr(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BARRE();
    antlr4::tree::TerminalNode* BARRE(size_t i);
    antlr4::tree::TerminalNode *LEFTBARRE();
    antlr4::tree::TerminalNode *LEFTNORM();
    antlr4::tree::TerminalNode *RIGHTBARRE();
    antlr4::tree::TerminalNode *RIGHTNORM();
    antlr4::tree::TerminalNode *UNDERSCORE();
    antlr4::tree::TerminalNode *LEFTSQ();
    antlr4::tree::TerminalNode *RIGHTSQ();

   
  };

  PrimaryContext* primary();

  class  Unary_exprContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    antlr4::Token *minusToken = nullptr;
    std::vector<antlr4::Token *> opS;
    ExprParser::PrimaryContext *primS = nullptr;
    ExprParser::PrimaryContext *sub = nullptr;
    antlr4::Token *factToken = nullptr;
    std::vector<antlr4::Token *> op;
    antlr4::Token *percentToken = nullptr;
    antlr4::Token *_tset254 = nullptr;
    antlr4::Token *identToken = nullptr;
    antlr4::Token *intToken = nullptr;
    ExprParser::PrimaryContext *subDown = nullptr;
    ExprParser::Add_exprContext *subUp = nullptr;
    antlr4::Token *fun = nullptr;
    ExprParser::Add_exprContext *firstArg = nullptr;
    ExprParser::Add_exprContext *add_exprContext = nullptr;
    std::vector<Add_exprContext *> othersArg;
    antlr4::Token *funcEmpty = nullptr;
    ExprParser::PrimaryContext *subFUNC = nullptr;
    antlr4::Token *func = nullptr;
    std::vector<Add_exprContext *> argFUNCT;
    antlr4::Token *indice = nullptr;
    ExprParser::Add_exprContext *under = nullptr;
    ExprParser::Add_exprContext *over = nullptr;
    ExprParser::Or_exprContext *cond = nullptr;
    antlr4::Token *overSumInt = nullptr;
    antlr4::Token *overSumI = nullptr;
    ExprParser::Add_exprContext *subSum = nullptr;
    ExprParser::Add_exprContext *underInt = nullptr;
    antlr4::Token *underIntINT = nullptr;
    antlr4::Token *underIntIDENT = nullptr;
    ExprParser::Add_exprContext *overInt = nullptr;
    antlr4::Token *overIntINT = nullptr;
    antlr4::Token *overIntIDENT = nullptr;
    ExprParser::Add_exprContext *subINT = nullptr;
    antlr4::Token *varInt = nullptr;
    Unary_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PrimaryContext *primary();
    antlr4::tree::TerminalNode *MINUS();
    std::vector<antlr4::tree::TerminalNode *> FACT();
    antlr4::tree::TerminalNode* FACT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> PERCENT();
    antlr4::tree::TerminalNode* PERCENT(size_t i);
    antlr4::tree::TerminalNode *CIRCUMFLEX();
    std::vector<antlr4::tree::TerminalNode *> IDENT();
    antlr4::tree::TerminalNode* IDENT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> INT();
    antlr4::tree::TerminalNode* INT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LEFTB();
    antlr4::tree::TerminalNode* LEFTB(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RIGHTB();
    antlr4::tree::TerminalNode* RIGHTB(size_t i);
    std::vector<Add_exprContext *> add_expr();
    Add_exprContext* add_expr(size_t i);
    antlr4::tree::TerminalNode *LEFTPAR();
    antlr4::tree::TerminalNode *RIGHTPAR();
    antlr4::tree::TerminalNode *FUNCTION();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *BigSUM();
    antlr4::tree::TerminalNode *UNDERSCORE();
    antlr4::tree::TerminalNode *EQUAL();
    Or_exprContext *or_expr();
    antlr4::tree::TerminalNode *INTEGRALE();
    antlr4::tree::TerminalNode *DERIVE();

   
  };

  Unary_exprContext* unary_expr();

  class  Mult_exprContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    ExprParser::Unary_exprContext *sub = nullptr;
    antlr4::Token *mulToken = nullptr;
    std::vector<antlr4::Token *> op;
    antlr4::Token *slashToken = nullptr;
    antlr4::Token *imulToken = nullptr;
    antlr4::Token *_tset605 = nullptr;
    ExprParser::Unary_exprContext *unary_exprContext = nullptr;
    std::vector<Unary_exprContext *> mult;
    Mult_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Unary_exprContext *> unary_expr();
    Unary_exprContext* unary_expr(size_t i);
    std::vector<antlr4::tree::TerminalNode *> IMUL();
    antlr4::tree::TerminalNode* IMUL(size_t i);
    std::vector<antlr4::tree::TerminalNode *> MUL();
    antlr4::tree::TerminalNode* MUL(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SLASH();
    antlr4::tree::TerminalNode* SLASH(size_t i);

   
  };

  Mult_exprContext* mult_expr();

  class  Add_exprContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    ExprParser::Mult_exprContext *sub = nullptr;
    antlr4::Token *addToken = nullptr;
    std::vector<antlr4::Token *> op;
    antlr4::Token *minusToken = nullptr;
    antlr4::Token *_tset645 = nullptr;
    ExprParser::Mult_exprContext *mult_exprContext = nullptr;
    std::vector<Mult_exprContext *> sum;
    Add_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Mult_exprContext *> mult_expr();
    Mult_exprContext* mult_expr(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ADD();
    antlr4::tree::TerminalNode* ADD(size_t i);
    std::vector<antlr4::tree::TerminalNode *> MINUS();
    antlr4::tree::TerminalNode* MINUS(size_t i);

   
  };

  Add_exprContext* add_expr();

  class  Primary_boolContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    antlr4::Token *identToken = nullptr;
    ExprParser::Or_exprContext *e = nullptr;
    ExprParser::Unary_exprContext *primLeft = nullptr;
    antlr4::Token *equalToken = nullptr;
    std::vector<antlr4::Token *> op;
    antlr4::Token *lessToken = nullptr;
    antlr4::Token *greaterToken = nullptr;
    antlr4::Token *notequalToken = nullptr;
    antlr4::Token *lessorequalToken = nullptr;
    antlr4::Token *greaterorequalToken = nullptr;
    antlr4::Token *_tset722 = nullptr;
    ExprParser::Unary_exprContext *primRight = nullptr;
    Primary_boolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FALSE();
    antlr4::tree::TerminalNode *TRUE();
    antlr4::tree::TerminalNode *IDENT();
    antlr4::tree::TerminalNode *LEFTPAR();
    antlr4::tree::TerminalNode *RIGHTPAR();
    Or_exprContext *or_expr();
    std::vector<Unary_exprContext *> unary_expr();
    Unary_exprContext* unary_expr(size_t i);
    antlr4::tree::TerminalNode *EQUAL();
    antlr4::tree::TerminalNode *LESS();
    antlr4::tree::TerminalNode *GREATER();
    antlr4::tree::TerminalNode *NotEQUAL();
    antlr4::tree::TerminalNode *LESSOREQUAL();
    antlr4::tree::TerminalNode *GREATEROREQUAL();

   
  };

  Primary_boolContext* primary_bool();

  class  Unary_boolContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    antlr4::Token *boolnotToken = nullptr;
    std::vector<antlr4::Token *> opS;
    ExprParser::Primary_boolContext *primS = nullptr;
    Unary_boolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Primary_boolContext *primary_bool();
    antlr4::tree::TerminalNode *BoolNOT();

   
  };

  Unary_boolContext* unary_bool();

  class  And_exprContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    ExprParser::Unary_boolContext *sub = nullptr;
    antlr4::Token *boolandToken = nullptr;
    std::vector<antlr4::Token *> op;
    ExprParser::Unary_boolContext *unary_boolContext = nullptr;
    std::vector<Unary_boolContext *> sum;
    And_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Unary_boolContext *> unary_bool();
    Unary_boolContext* unary_bool(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BoolAND();
    antlr4::tree::TerminalNode* BoolAND(size_t i);

   
  };

  And_exprContext* and_expr();

  class  Or_exprContext : public antlr4::ParserRuleContext {
  public:
    ExprPtr node;
    ExprParser::And_exprContext *sub = nullptr;
    antlr4::Token *boolorToken = nullptr;
    std::vector<antlr4::Token *> op;
    ExprParser::And_exprContext *and_exprContext = nullptr;
    std::vector<And_exprContext *> sum;
    Or_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<And_exprContext *> and_expr();
    And_exprContext* and_expr(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BoolOR();
    antlr4::tree::TerminalNode* BoolOR(size_t i);

   
  };

  Or_exprContext* or_expr();


  // By default the static state used to implement the parser is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
};

