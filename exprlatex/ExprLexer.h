
// Generated from ExprLexer.g4 by ANTLR 4.13.2

#pragma once


#include "antlr4-runtime.h"




class  ExprLexer : public antlr4::Lexer {
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

  explicit ExprLexer(antlr4::CharStream *input);

  ~ExprLexer() override;


  std::string getGrammarFileName() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const std::vector<std::string>& getChannelNames() const override;

  const std::vector<std::string>& getModeNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;

  const antlr4::atn::ATN& getATN() const override;

  // By default the static state used to implement the lexer is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:

  // Individual action functions triggered by action() above.

  // Individual semantic predicate functions triggered by sempred() above.

};

