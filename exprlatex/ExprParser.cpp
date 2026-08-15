
#include "Expr.h"
#include "tools.h"
#include <stdio.h>
#include <iostream>


// Generated from ExprParser.g4 by ANTLR 4.13.2



#include "ExprParser.h"


using namespace antlrcpp;

using namespace antlr4;

namespace {

struct ExprParserStaticData final {
  ExprParserStaticData(std::vector<std::string> ruleNames,
                        std::vector<std::string> literalNames,
                        std::vector<std::string> symbolicNames)
      : ruleNames(std::move(ruleNames)), literalNames(std::move(literalNames)),
        symbolicNames(std::move(symbolicNames)),
        vocabulary(this->literalNames, this->symbolicNames) {}

  ExprParserStaticData(const ExprParserStaticData&) = delete;
  ExprParserStaticData(ExprParserStaticData&&) = delete;
  ExprParserStaticData& operator=(const ExprParserStaticData&) = delete;
  ExprParserStaticData& operator=(ExprParserStaticData&&) = delete;

  std::vector<antlr4::dfa::DFA> decisionToDFA;
  antlr4::atn::PredictionContextCache sharedContextCache;
  const std::vector<std::string> ruleNames;
  const std::vector<std::string> literalNames;
  const std::vector<std::string> symbolicNames;
  const antlr4::dfa::Vocabulary vocabulary;
  antlr4::atn::SerializedATNView serializedATN;
  std::unique_ptr<antlr4::atn::ATN> atn;
};

::antlr4::internal::OnceFlag exprparserParserOnceFlag;
#if ANTLR4_USE_THREAD_LOCAL_CACHE
static thread_local
#endif
std::unique_ptr<ExprParserStaticData> exprparserParserStaticData = nullptr;

void exprparserParserInitialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  if (exprparserParserStaticData != nullptr) {
    return;
  }
#else
  assert(exprparserParserStaticData == nullptr);
#endif
  auto staticData = std::make_unique<ExprParserStaticData>(
    std::vector<std::string>{
      "start", "primary", "unary_expr", "mult_expr", "add_expr", "primary_bool", 
      "unary_bool", "and_expr", "or_expr"
    },
    std::vector<std::string>{
      "", "", "", "", "", "", "", "", "", "", "", "", "", "'+'", "'-'", 
      "'!'", "'\\%'", "'^'", "'/'", "", "", "", "", "", "", "", "", "'\\'", 
      "'&'", "'{'", "'}'", "'['", "']'", "'_'", "','", "'|'"
    },
    std::vector<std::string>{
      "", "IMUL", "WS", "IGNORE_SPACE_COMMAND", "LINE_COMMENT", "BigSUM", 
      "INTEGRALE", "DERIVE", "INT", "DOUBLE", "DOUBLEExt", "DIGIT", "MUL", 
      "ADD", "MINUS", "FACT", "PERCENT", "CIRCUMFLEX", "SLASH", "EQUAL", 
      "LESS", "GREATER", "NotEQUAL", "LESSOREQUAL", "GREATEROREQUAL", "LEFTPAR", 
      "RIGHTPAR", "BACKSLASH", "AMPERSAND", "LEFTB", "RIGHTB", "LEFTSQ", 
      "RIGHTSQ", "UNDERSCORE", "COMMA", "BARRE", "LEFTBARRE", "RIGHTBARRE", 
      "LEFTNORM", "RIGHTNORM", "FALSE", "TRUE", "BoolAND", "BoolOR", "BoolNOT", 
      "IDENT", "FUNCTION", "LETTER"
    }
  );
  static const int32_t serializedATNSegment[] = {
  	4,1,47,270,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,6,2,
  	7,7,7,2,8,7,8,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  	1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,66,
  	8,1,1,2,1,2,3,2,70,8,2,1,2,1,2,1,2,1,2,1,2,4,2,77,8,2,11,2,12,2,78,1,
  	2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,
  	1,2,1,2,1,2,1,2,1,2,3,2,104,8,2,1,2,1,2,1,2,1,2,5,2,110,8,2,10,2,12,2,
  	113,9,2,1,2,1,2,3,2,117,8,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,
  	2,4,2,130,8,2,11,2,12,2,131,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,
  	2,1,2,1,2,1,2,1,2,1,2,3,2,150,8,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,
  	160,8,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,
  	2,177,8,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,190,8,2,1,2,
  	1,2,1,2,1,2,1,2,1,2,1,2,3,2,199,8,2,1,3,3,3,202,8,3,1,3,1,3,1,3,5,3,207,
  	8,3,10,3,12,3,210,9,3,1,3,1,3,1,4,1,4,1,4,5,4,217,8,4,10,4,12,4,220,9,
  	4,1,4,1,4,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,
  	1,5,1,5,3,5,241,8,5,1,6,1,6,3,6,245,8,6,1,6,1,6,1,6,1,7,1,7,1,7,5,7,253,
  	8,7,10,7,12,7,256,9,7,1,7,1,7,1,8,1,8,1,8,5,8,263,8,8,10,8,12,8,266,9,
  	8,1,8,1,8,1,8,0,0,9,0,2,4,6,8,10,12,14,16,0,6,2,0,35,36,38,38,3,0,35,
  	35,37,37,39,39,1,0,15,16,3,0,1,1,12,12,18,18,1,0,13,14,1,0,19,24,301,
  	0,18,1,0,0,0,2,65,1,0,0,0,4,198,1,0,0,0,6,201,1,0,0,0,8,213,1,0,0,0,10,
  	240,1,0,0,0,12,244,1,0,0,0,14,249,1,0,0,0,16,259,1,0,0,0,18,19,3,8,4,
  	0,19,20,5,0,0,1,20,21,6,0,-1,0,21,1,1,0,0,0,22,23,5,8,0,0,23,66,6,1,-1,
  	0,24,25,5,9,0,0,25,66,6,1,-1,0,26,27,5,10,0,0,27,66,6,1,-1,0,28,29,5,
  	45,0,0,29,66,6,1,-1,0,30,31,5,25,0,0,31,32,3,8,4,0,32,33,5,26,0,0,33,
  	34,6,1,-1,0,34,66,1,0,0,0,35,36,7,0,0,0,36,37,3,8,4,0,37,38,7,1,0,0,38,
  	39,6,1,-1,0,39,66,1,0,0,0,40,41,5,38,0,0,41,42,3,8,4,0,42,43,5,39,0,0,
  	43,44,5,33,0,0,44,45,5,45,0,0,45,46,6,1,-1,0,46,66,1,0,0,0,47,48,5,25,
  	0,0,48,49,3,8,4,0,49,50,5,26,0,0,50,51,5,31,0,0,51,52,3,8,4,0,52,53,5,
  	32,0,0,53,54,6,1,-1,0,54,66,1,0,0,0,55,56,5,45,0,0,56,57,5,31,0,0,57,
  	58,3,8,4,0,58,59,5,32,0,0,59,60,6,1,-1,0,60,66,1,0,0,0,61,62,5,45,0,0,
  	62,63,5,33,0,0,63,64,5,45,0,0,64,66,6,1,-1,0,65,22,1,0,0,0,65,24,1,0,
  	0,0,65,26,1,0,0,0,65,28,1,0,0,0,65,30,1,0,0,0,65,35,1,0,0,0,65,40,1,0,
  	0,0,65,47,1,0,0,0,65,55,1,0,0,0,65,61,1,0,0,0,66,3,1,0,0,0,67,68,5,14,
  	0,0,68,70,6,2,-1,0,69,67,1,0,0,0,69,70,1,0,0,0,70,71,1,0,0,0,71,72,3,
  	2,1,0,72,73,6,2,-1,0,73,199,1,0,0,0,74,76,3,2,1,0,75,77,7,2,0,0,76,75,
  	1,0,0,0,77,78,1,0,0,0,78,76,1,0,0,0,78,79,1,0,0,0,79,80,1,0,0,0,80,81,
  	6,2,-1,0,81,199,1,0,0,0,82,83,3,2,1,0,83,84,5,17,0,0,84,85,5,45,0,0,85,
  	86,6,2,-1,0,86,199,1,0,0,0,87,88,3,2,1,0,88,89,5,17,0,0,89,90,5,8,0,0,
  	90,91,6,2,-1,0,91,199,1,0,0,0,92,93,3,2,1,0,93,94,5,17,0,0,94,95,5,29,
  	0,0,95,96,3,8,4,0,96,97,5,30,0,0,97,98,6,2,-1,0,98,199,1,0,0,0,99,100,
  	5,45,0,0,100,104,6,2,-1,0,101,102,5,46,0,0,102,104,6,2,-1,0,103,99,1,
  	0,0,0,103,101,1,0,0,0,104,105,1,0,0,0,105,116,5,25,0,0,106,111,3,8,4,
  	0,107,108,5,34,0,0,108,110,3,8,4,0,109,107,1,0,0,0,110,113,1,0,0,0,111,
  	109,1,0,0,0,111,112,1,0,0,0,112,114,1,0,0,0,113,111,1,0,0,0,114,115,6,
  	2,-1,0,115,117,1,0,0,0,116,106,1,0,0,0,116,117,1,0,0,0,117,118,1,0,0,
  	0,118,119,5,26,0,0,119,199,6,2,-1,0,120,121,5,46,0,0,121,122,3,2,1,0,
  	122,123,6,2,-1,0,123,199,1,0,0,0,124,129,5,46,0,0,125,126,5,29,0,0,126,
  	127,3,8,4,0,127,128,5,30,0,0,128,130,1,0,0,0,129,125,1,0,0,0,130,131,
  	1,0,0,0,131,129,1,0,0,0,131,132,1,0,0,0,132,133,1,0,0,0,133,134,6,2,-1,
  	0,134,199,1,0,0,0,135,136,5,5,0,0,136,137,5,33,0,0,137,138,5,29,0,0,138,
  	139,5,45,0,0,139,140,5,19,0,0,140,141,3,8,4,0,141,142,5,30,0,0,142,159,
  	5,17,0,0,143,144,5,29,0,0,144,149,3,8,4,0,145,146,5,34,0,0,146,147,3,
  	16,8,0,147,148,6,2,-1,0,148,150,1,0,0,0,149,145,1,0,0,0,149,150,1,0,0,
  	0,150,151,1,0,0,0,151,152,5,30,0,0,152,153,1,0,0,0,153,154,6,2,-1,0,154,
  	160,1,0,0,0,155,156,5,8,0,0,156,160,6,2,-1,0,157,158,5,45,0,0,158,160,
  	6,2,-1,0,159,143,1,0,0,0,159,155,1,0,0,0,159,157,1,0,0,0,160,161,1,0,
  	0,0,161,162,3,8,4,0,162,163,6,2,-1,0,163,199,1,0,0,0,164,165,5,6,0,0,
  	165,176,5,33,0,0,166,167,5,29,0,0,167,168,3,8,4,0,168,169,5,30,0,0,169,
  	170,1,0,0,0,170,171,6,2,-1,0,171,177,1,0,0,0,172,173,5,8,0,0,173,177,
  	6,2,-1,0,174,175,5,45,0,0,175,177,6,2,-1,0,176,166,1,0,0,0,176,172,1,
  	0,0,0,176,174,1,0,0,0,177,178,1,0,0,0,178,189,5,17,0,0,179,180,5,29,0,
  	0,180,181,3,8,4,0,181,182,5,30,0,0,182,183,1,0,0,0,183,184,6,2,-1,0,184,
  	190,1,0,0,0,185,186,5,8,0,0,186,190,6,2,-1,0,187,188,5,45,0,0,188,190,
  	6,2,-1,0,189,179,1,0,0,0,189,185,1,0,0,0,189,187,1,0,0,0,190,191,1,0,
  	0,0,191,192,3,8,4,0,192,193,5,7,0,0,193,194,5,29,0,0,194,195,5,45,0,0,
  	195,196,5,30,0,0,196,197,6,2,-1,0,197,199,1,0,0,0,198,69,1,0,0,0,198,
  	74,1,0,0,0,198,82,1,0,0,0,198,87,1,0,0,0,198,92,1,0,0,0,198,103,1,0,0,
  	0,198,120,1,0,0,0,198,124,1,0,0,0,198,135,1,0,0,0,198,164,1,0,0,0,199,
  	5,1,0,0,0,200,202,5,1,0,0,201,200,1,0,0,0,201,202,1,0,0,0,202,203,1,0,
  	0,0,203,208,3,4,2,0,204,205,7,3,0,0,205,207,3,4,2,0,206,204,1,0,0,0,207,
  	210,1,0,0,0,208,206,1,0,0,0,208,209,1,0,0,0,209,211,1,0,0,0,210,208,1,
  	0,0,0,211,212,6,3,-1,0,212,7,1,0,0,0,213,218,3,6,3,0,214,215,7,4,0,0,
  	215,217,3,6,3,0,216,214,1,0,0,0,217,220,1,0,0,0,218,216,1,0,0,0,218,219,
  	1,0,0,0,219,221,1,0,0,0,220,218,1,0,0,0,221,222,6,4,-1,0,222,9,1,0,0,
  	0,223,224,5,40,0,0,224,241,6,5,-1,0,225,226,5,41,0,0,226,241,6,5,-1,0,
  	227,228,5,45,0,0,228,241,6,5,-1,0,229,230,5,25,0,0,230,231,3,16,8,0,231,
  	232,5,26,0,0,232,233,6,5,-1,0,233,241,1,0,0,0,234,235,3,4,2,0,235,236,
  	7,5,0,0,236,237,3,4,2,0,237,238,1,0,0,0,238,239,6,5,-1,0,239,241,1,0,
  	0,0,240,223,1,0,0,0,240,225,1,0,0,0,240,227,1,0,0,0,240,229,1,0,0,0,240,
  	234,1,0,0,0,241,11,1,0,0,0,242,243,5,44,0,0,243,245,6,6,-1,0,244,242,
  	1,0,0,0,244,245,1,0,0,0,245,246,1,0,0,0,246,247,3,10,5,0,247,248,6,6,
  	-1,0,248,13,1,0,0,0,249,254,3,12,6,0,250,251,5,42,0,0,251,253,3,12,6,
  	0,252,250,1,0,0,0,253,256,1,0,0,0,254,252,1,0,0,0,254,255,1,0,0,0,255,
  	257,1,0,0,0,256,254,1,0,0,0,257,258,6,7,-1,0,258,15,1,0,0,0,259,264,3,
  	14,7,0,260,261,5,43,0,0,261,263,3,14,7,0,262,260,1,0,0,0,263,266,1,0,
  	0,0,264,262,1,0,0,0,264,265,1,0,0,0,265,267,1,0,0,0,266,264,1,0,0,0,267,
  	268,6,8,-1,0,268,17,1,0,0,0,19,65,69,78,103,111,116,131,149,159,176,189,
  	198,201,208,218,240,244,254,264
  };
  staticData->serializedATN = antlr4::atn::SerializedATNView(serializedATNSegment, sizeof(serializedATNSegment) / sizeof(serializedATNSegment[0]));

  antlr4::atn::ATNDeserializer deserializer;
  staticData->atn = deserializer.deserialize(staticData->serializedATN);

  const size_t count = staticData->atn->getNumberOfDecisions();
  staticData->decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    staticData->decisionToDFA.emplace_back(staticData->atn->getDecisionState(i), i);
  }
  exprparserParserStaticData = std::move(staticData);
}

}

ExprParser::ExprParser(TokenStream *input) : ExprParser(input, antlr4::atn::ParserATNSimulatorOptions()) {}

ExprParser::ExprParser(TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options) : Parser(input) {
  ExprParser::initialize();
  _interpreter = new atn::ParserATNSimulator(this, *exprparserParserStaticData->atn, exprparserParserStaticData->decisionToDFA, exprparserParserStaticData->sharedContextCache, options);
}

ExprParser::~ExprParser() {
  delete _interpreter;
}

const atn::ATN& ExprParser::getATN() const {
  return *exprparserParserStaticData->atn;
}

std::string ExprParser::getGrammarFileName() const {
  return "ExprParser.g4";
}

const std::vector<std::string>& ExprParser::getRuleNames() const {
  return exprparserParserStaticData->ruleNames;
}

const dfa::Vocabulary& ExprParser::getVocabulary() const {
  return exprparserParserStaticData->vocabulary;
}

antlr4::atn::SerializedATNView ExprParser::getSerializedATN() const {
  return exprparserParserStaticData->serializedATN;
}


//----------------- StartContext ------------------------------------------------------------------

ExprParser::StartContext::StartContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExprParser::StartContext::EOF() {
  return getToken(ExprParser::EOF, 0);
}

ExprParser::Add_exprContext* ExprParser::StartContext::add_expr() {
  return getRuleContext<ExprParser::Add_exprContext>(0);
}


size_t ExprParser::StartContext::getRuleIndex() const {
  return ExprParser::RuleStart;
}


ExprParser::StartContext* ExprParser::start() {
  StartContext *_localctx = _tracker.createInstance<StartContext>(_ctx, getState());
  enterRule(_localctx, 0, ExprParser::RuleStart);

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(18);
    antlrcpp::downCast<StartContext *>(_localctx)->e = add_expr();
    setState(19);
    match(ExprParser::EOF);
     antlrcpp::downCast<StartContext *>(_localctx)->node = antlrcpp::downCast<StartContext *>(_localctx)->e->node; 
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PrimaryContext ------------------------------------------------------------------

ExprParser::PrimaryContext::PrimaryContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExprParser::PrimaryContext::INT() {
  return getToken(ExprParser::INT, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::DOUBLE() {
  return getToken(ExprParser::DOUBLE, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::DOUBLEExt() {
  return getToken(ExprParser::DOUBLEExt, 0);
}

std::vector<tree::TerminalNode *> ExprParser::PrimaryContext::IDENT() {
  return getTokens(ExprParser::IDENT);
}

tree::TerminalNode* ExprParser::PrimaryContext::IDENT(size_t i) {
  return getToken(ExprParser::IDENT, i);
}

tree::TerminalNode* ExprParser::PrimaryContext::LEFTPAR() {
  return getToken(ExprParser::LEFTPAR, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::RIGHTPAR() {
  return getToken(ExprParser::RIGHTPAR, 0);
}

std::vector<ExprParser::Add_exprContext *> ExprParser::PrimaryContext::add_expr() {
  return getRuleContexts<ExprParser::Add_exprContext>();
}

ExprParser::Add_exprContext* ExprParser::PrimaryContext::add_expr(size_t i) {
  return getRuleContext<ExprParser::Add_exprContext>(i);
}

std::vector<tree::TerminalNode *> ExprParser::PrimaryContext::BARRE() {
  return getTokens(ExprParser::BARRE);
}

tree::TerminalNode* ExprParser::PrimaryContext::BARRE(size_t i) {
  return getToken(ExprParser::BARRE, i);
}

tree::TerminalNode* ExprParser::PrimaryContext::LEFTBARRE() {
  return getToken(ExprParser::LEFTBARRE, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::LEFTNORM() {
  return getToken(ExprParser::LEFTNORM, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::RIGHTBARRE() {
  return getToken(ExprParser::RIGHTBARRE, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::RIGHTNORM() {
  return getToken(ExprParser::RIGHTNORM, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::UNDERSCORE() {
  return getToken(ExprParser::UNDERSCORE, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::LEFTSQ() {
  return getToken(ExprParser::LEFTSQ, 0);
}

tree::TerminalNode* ExprParser::PrimaryContext::RIGHTSQ() {
  return getToken(ExprParser::RIGHTSQ, 0);
}


size_t ExprParser::PrimaryContext::getRuleIndex() const {
  return ExprParser::RulePrimary;
}


ExprParser::PrimaryContext* ExprParser::primary() {
  PrimaryContext *_localctx = _tracker.createInstance<PrimaryContext>(_ctx, getState());
  enterRule(_localctx, 2, ExprParser::RulePrimary);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(65);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 0, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(22);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->intToken = match(ExprParser::INT);
       
               antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_unique<IntNode>(std::stoi((antlrcpp::downCast<PrimaryContext *>(_localctx)->intToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->intToken->getText() : ""))); 
               //std::cout << TypeNodeToString(_localctx->node->type) << std::endl;
               //printf("%s", TypeNodeToString(_localctx->node->getType()));
              
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(24);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->doubleToken = match(ExprParser::DOUBLE);
       
                    antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_unique<DoubleNode>(std::stold((antlrcpp::downCast<PrimaryContext *>(_localctx)->doubleToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->doubleToken->getText() : "")));
                   
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(26);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->doubleextToken = match(ExprParser::DOUBLEExt);
       
                       antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_unique<DoubleNode>(std::stold((antlrcpp::downCast<PrimaryContext *>(_localctx)->doubleextToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->doubleextToken->getText() : "")));
                      
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(28);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken = match(ExprParser::IDENT);
       
                   antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_unique<IdentNode>((antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken->getText() : "")[0]);
                  
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(30);
      match(ExprParser::LEFTPAR);
      setState(31);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->e = add_expr();
      setState(32);
      match(ExprParser::RIGHTPAR);
       
              antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  antlrcpp::downCast<PrimaryContext *>(_localctx)->e->node; 
             
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(35);
      _la = _input->LA(1);
      if (!((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 377957122048) != 0))) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(36);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->norm = add_expr();
      setState(37);
      _la = _input->LA(1);
      if (!((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 721554505728) != 0))) {
      _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
       

                   if (antlrcpp::downCast<PrimaryContext *>(_localctx)->norm->node == nullptr)
                      throw std::invalid_argument( "SYNTAX ERROR @ 'Euclidian Norm' RULE" );

                  antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>(
                          "EuclideanNorm",
                          antlrcpp::downCast<PrimaryContext *>(_localctx)->norm->node
                      );
             
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(40);
      match(ExprParser::LEFTNORM);
      setState(41);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->norm = add_expr();
      setState(42);
      match(ExprParser::RIGHTNORM);
      setState(43);
      match(ExprParser::UNDERSCORE);
      setState(44);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken = match(ExprParser::IDENT);
       
                  if (antlrcpp::downCast<PrimaryContext *>(_localctx)->norm->node == nullptr)
                      throw std::invalid_argument( "SYNTAX ERROR @ 'Frobenius Norm' RULE" );

                  if ((antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken->getText() : "")[0] == 'F' || (antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken->getText() : "")[0] == 'f')
                      antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>(
                              "FrobeniusNorm",
                              antlrcpp::downCast<PrimaryContext *>(_localctx)->norm->node
                          );
                  else
                      throw std::invalid_argument( "ERROR = NORM WITH STRANGE ARGUMENTS !" );
             
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(47);
      match(ExprParser::LEFTPAR);
      setState(48);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->sub = add_expr();
      setState(49);
      match(ExprParser::RIGHTPAR);
      setState(50);
      match(ExprParser::LEFTSQ);
      setState(51);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->indice = add_expr();
      setState(52);
      match(ExprParser::RIGHTSQ);
       
                  if ( (antlrcpp::downCast<PrimaryContext *>(_localctx)->sub->node == nullptr) || (antlrcpp::downCast<PrimaryContext *>(_localctx)->indice->node == nullptr))
                      throw std::invalid_argument( "SYNTAX ERROR @ 'Vector accessess' RULE" );
                  
                  antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                          "VectorAccess",
                          antlrcpp::downCast<PrimaryContext *>(_localctx)->sub->node,
                          antlrcpp::downCast<PrimaryContext *>(_localctx)->indice->node
                      );
             
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(55);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken = match(ExprParser::IDENT);
      setState(56);
      match(ExprParser::LEFTSQ);
      setState(57);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->indiceI = add_expr();
      setState(58);
      match(ExprParser::RIGHTSQ);

                  if (antlrcpp::downCast<PrimaryContext *>(_localctx)->indiceI->node == nullptr)
                      throw std::invalid_argument( "SYNTAX ERROR @ 'Vector accessess of ident' RULE" );

                  antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                          "VectorAccess",
                          std::make_unique<IdentNode>((antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->identToken->getText() : "")[0]),
                          antlrcpp::downCast<PrimaryContext *>(_localctx)->indiceI->node
                      );
              
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(61);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->vector = match(ExprParser::IDENT);
      setState(62);
      match(ExprParser::UNDERSCORE);
      setState(63);
      antlrcpp::downCast<PrimaryContext *>(_localctx)->indiceVI = match(ExprParser::IDENT);

                  antlrcpp::downCast<PrimaryContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                          "VectorAccess",
                          std::make_unique<IdentNode>((antlrcpp::downCast<PrimaryContext *>(_localctx)->vector != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->vector->getText() : "")[0]),
                          std::make_unique<IdentNode>((antlrcpp::downCast<PrimaryContext *>(_localctx)->indiceVI != nullptr ? antlrcpp::downCast<PrimaryContext *>(_localctx)->indiceVI->getText() : "")[0])
                      );
              
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Unary_exprContext ------------------------------------------------------------------

ExprParser::Unary_exprContext::Unary_exprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExprParser::PrimaryContext* ExprParser::Unary_exprContext::primary() {
  return getRuleContext<ExprParser::PrimaryContext>(0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::MINUS() {
  return getToken(ExprParser::MINUS, 0);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::FACT() {
  return getTokens(ExprParser::FACT);
}

tree::TerminalNode* ExprParser::Unary_exprContext::FACT(size_t i) {
  return getToken(ExprParser::FACT, i);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::PERCENT() {
  return getTokens(ExprParser::PERCENT);
}

tree::TerminalNode* ExprParser::Unary_exprContext::PERCENT(size_t i) {
  return getToken(ExprParser::PERCENT, i);
}

tree::TerminalNode* ExprParser::Unary_exprContext::CIRCUMFLEX() {
  return getToken(ExprParser::CIRCUMFLEX, 0);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::IDENT() {
  return getTokens(ExprParser::IDENT);
}

tree::TerminalNode* ExprParser::Unary_exprContext::IDENT(size_t i) {
  return getToken(ExprParser::IDENT, i);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::INT() {
  return getTokens(ExprParser::INT);
}

tree::TerminalNode* ExprParser::Unary_exprContext::INT(size_t i) {
  return getToken(ExprParser::INT, i);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::LEFTB() {
  return getTokens(ExprParser::LEFTB);
}

tree::TerminalNode* ExprParser::Unary_exprContext::LEFTB(size_t i) {
  return getToken(ExprParser::LEFTB, i);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::RIGHTB() {
  return getTokens(ExprParser::RIGHTB);
}

tree::TerminalNode* ExprParser::Unary_exprContext::RIGHTB(size_t i) {
  return getToken(ExprParser::RIGHTB, i);
}

std::vector<ExprParser::Add_exprContext *> ExprParser::Unary_exprContext::add_expr() {
  return getRuleContexts<ExprParser::Add_exprContext>();
}

ExprParser::Add_exprContext* ExprParser::Unary_exprContext::add_expr(size_t i) {
  return getRuleContext<ExprParser::Add_exprContext>(i);
}

tree::TerminalNode* ExprParser::Unary_exprContext::LEFTPAR() {
  return getToken(ExprParser::LEFTPAR, 0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::RIGHTPAR() {
  return getToken(ExprParser::RIGHTPAR, 0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::FUNCTION() {
  return getToken(ExprParser::FUNCTION, 0);
}

std::vector<tree::TerminalNode *> ExprParser::Unary_exprContext::COMMA() {
  return getTokens(ExprParser::COMMA);
}

tree::TerminalNode* ExprParser::Unary_exprContext::COMMA(size_t i) {
  return getToken(ExprParser::COMMA, i);
}

tree::TerminalNode* ExprParser::Unary_exprContext::BigSUM() {
  return getToken(ExprParser::BigSUM, 0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::UNDERSCORE() {
  return getToken(ExprParser::UNDERSCORE, 0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::EQUAL() {
  return getToken(ExprParser::EQUAL, 0);
}

ExprParser::Or_exprContext* ExprParser::Unary_exprContext::or_expr() {
  return getRuleContext<ExprParser::Or_exprContext>(0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::INTEGRALE() {
  return getToken(ExprParser::INTEGRALE, 0);
}

tree::TerminalNode* ExprParser::Unary_exprContext::DERIVE() {
  return getToken(ExprParser::DERIVE, 0);
}


size_t ExprParser::Unary_exprContext::getRuleIndex() const {
  return ExprParser::RuleUnary_expr;
}


ExprParser::Unary_exprContext* ExprParser::unary_expr() {
  Unary_exprContext *_localctx = _tracker.createInstance<Unary_exprContext>(_ctx, getState());
  enterRule(_localctx, 4, ExprParser::RuleUnary_expr);
  bool empty = true; int multiChoix1 = 0; int multiChoix2 = 0; 
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(198);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(69);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == ExprParser::MINUS) {
        setState(67);
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->minusToken = match(ExprParser::MINUS);
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->opS.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->minusToken);
        empty = false;
      }
      setState(71);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->primS = primary();
       
                  if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->primS->node == nullptr)
                      throw std::invalid_argument( "SYNTAX ERROR @ '-prim' RULE" );
                  
                  // if no unary_operator
                  if (empty)
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->node = antlrcpp::downCast<Unary_exprContext *>(_localctx)->primS->node;
                  else {
                       if (auto intNode = dynamic_cast<IntNode*>(antlrcpp::downCast<Unary_exprContext *>(_localctx)->primS->node.get()))
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_unique<IntNode>(-intNode->value);
                       else
                       if (auto doubleNode = dynamic_cast<DoubleNode*>(antlrcpp::downCast<Unary_exprContext *>(_localctx)->primS->node.get()))
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_unique<DoubleNode>(-doubleNode->value);
                          
                      else
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>("-",antlrcpp::downCast<Unary_exprContext *>(_localctx)->primS->node);
                  }
              
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(74);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub = primary();
      setState(76); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(75);
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->_tset254 = _input->LT(1);
        _la = _input->LA(1);
        if (!(_la == ExprParser::FACT

        || _la == ExprParser::PERCENT)) {
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->_tset254 = _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->op.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->_tset254);
        setState(78); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == ExprParser::FACT

      || _la == ExprParser::PERCENT);
       
                  if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node == nullptr)
                      throw std::invalid_argument( "SYNTAX ERROR @ 'prim! or prim%' RULE" );
                  
                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node;
                  for (int i = 0; i < antlrcpp::downCast<Unary_exprContext *>(_localctx)->op.size(); ++i) {
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>(
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->op[i]->getText(),
                          _localctx->node
                      );
                  }
              
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(82);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub = primary();
      setState(83);
      match(ExprParser::CIRCUMFLEX);
      setState(84);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->identToken = match(ExprParser::IDENT);

              if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node == nullptr)
                  throw std::invalid_argument( "SYNTAX ERROR @ 'prim^a' RULE" );
              
              if ((antlrcpp::downCast<Unary_exprContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->identToken->getText() : "")[0] == 'T')
                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>("Transpose",antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node);
              else
                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                          "^",
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node,
                          std::make_unique<IdentNode>((antlrcpp::downCast<Unary_exprContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->identToken->getText() : "")[0])
                      );
            
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(87);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub = primary();
      setState(88);
      match(ExprParser::CIRCUMFLEX);
      setState(89);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->intToken = match(ExprParser::INT);

              if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node == nullptr)
                  throw std::invalid_argument( "SYNTAX ERROR @ 'prim^2' RULE" );

              int how = std::stoi((antlrcpp::downCast<Unary_exprContext *>(_localctx)->intToken != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->intToken->getText() : "")); 
              if (how > 9) {
                  throw std::invalid_argument( "ERROR = POWER TO AN INTEGER > 9 !" );
              }
              antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                          "^",
                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->sub->node,
                          std::make_unique<IntNode>(how)
                      );
            
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(92);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subDown = primary();
      setState(93);
      match(ExprParser::CIRCUMFLEX);
      setState(94);
      match(ExprParser::LEFTB);
      setState(95);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subUp = add_expr();
      setState(96);
      match(ExprParser::RIGHTB);

              if ((antlrcpp::downCast<Unary_exprContext *>(_localctx)->subDown->node == nullptr) || (antlrcpp::downCast<Unary_exprContext *>(_localctx)->subUp->node == nullptr))
                  throw std::invalid_argument( "SYNTAX ERROR @ 'prim^{expr}' RULE" );
              
              if (auto intNode = dynamic_cast<IntNode*>(antlrcpp::downCast<Unary_exprContext *>(_localctx)->subUp->node.get()))
                  if (intNode->value == -1)
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>(
                              "Inverse",
                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subDown->node
                          );
                  else 
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                              "^",
                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subDown->node,
                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subUp->node
                          );
              else
              if (auto identNode = dynamic_cast<IdentNode*>(antlrcpp::downCast<Unary_exprContext *>(_localctx)->subUp->node.get()))
                  if (identNode->value == 'T')
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>(
                              "Transpose",
                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subDown->node
                          );
                  else
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                              "^",
                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subDown->node,
                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subUp->node
                          );
           
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(103);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case ExprParser::IDENT: {
          setState(99);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->fun = match(ExprParser::IDENT);
          multiChoix1 = 1;
          break;
        }

        case ExprParser::FUNCTION: {
          setState(101);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->fun = match(ExprParser::FUNCTION);
          multiChoix1 = 2;
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(105);
      match(ExprParser::LEFTPAR);
      setState(116);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 105931106961250) != 0)) {
        setState(106);
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->firstArg = add_expr();
        setState(111);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == ExprParser::COMMA) {
          setState(107);
          match(ExprParser::COMMA);
          setState(108);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->add_exprContext = add_expr();
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->othersArg.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->add_exprContext);
          setState(113);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        empty = false;
      }
      setState(118);
      match(ExprParser::RIGHTPAR);

              if ((antlrcpp::downCast<Unary_exprContext *>(_localctx)->firstArg->node == nullptr) || (validateVector(antlrcpp::downCast<Unary_exprContext *>(_localctx)->othersArg)))
                  throw std::invalid_argument( "SYNTAX ERROR @ 'f or \\fun (expr,...,expr)' RULE" );        
              
              // si pas d'arguments
              if (empty) {
                  std::vector<ExprPtr> emptyVector;
                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<FunCallNode>(((antlrcpp::downCast<Unary_exprContext *>(_localctx)->fun != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->fun->getText() : "")),emptyVector);
              }
              else {
                  std::vector<ExprPtr> args;
                  args.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->firstArg->node);
                  for (int i = 0; i < antlrcpp::downCast<Unary_exprContext *>(_localctx)->othersArg.size(); ++i)
                      args.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->othersArg[i]->node);
                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<FunCallNode>(((antlrcpp::downCast<Unary_exprContext *>(_localctx)->fun != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->fun->getText() : "")),args);
              }
            
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(120);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->funcEmpty = match(ExprParser::FUNCTION);
      setState(121);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subFUNC = primary();

              if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->subFUNC->node == nullptr)
                  throw std::invalid_argument( "SYNTAX ERROR @ '\\fun prim' RULE" );

              std::vector<ExprPtr> args;
              args.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->subFUNC->node);
              antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<FunCallNode>(((antlrcpp::downCast<Unary_exprContext *>(_localctx)->funcEmpty != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->funcEmpty->getText() : "")),args);
           
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(124);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->func = match(ExprParser::FUNCTION);
      setState(129); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(125);
        match(ExprParser::LEFTB);
        setState(126);
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->add_exprContext = add_expr();
        antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->add_exprContext);
        setState(127);
        match(ExprParser::RIGHTB);
        setState(131); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == ExprParser::LEFTB);

              if (validateVector(antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT))
                  throw std::invalid_argument( "SYNTAX ERROR @ '\\func{}{}...{}' RULE" );

              std::string op =  fromFunctionToOperation(antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT.size(), (antlrcpp::downCast<Unary_exprContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->func->getText() : ""));
              if (op!=" ") {
                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =   std::make_shared<BinaryOpNode>(
                      op,
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT[0]->node,
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT[1]->node
                  );
              }
              else {
                      std::vector<ExprPtr> args;
                      for (int i = 0; i < antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT.size(); ++i)
                          args.push_back(antlrcpp::downCast<Unary_exprContext *>(_localctx)->argFUNCT[i]->node);
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<FunCallNode>((antlrcpp::downCast<Unary_exprContext *>(_localctx)->func != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->func->getText() : ""),args);
                  }
            
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(135);
      match(ExprParser::BigSUM);
      setState(136);
      match(ExprParser::UNDERSCORE);
      setState(137);
      match(ExprParser::LEFTB);
      setState(138);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->indice = match(ExprParser::IDENT);
      setState(139);
      match(ExprParser::EQUAL);
      setState(140);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->under = add_expr();
      setState(141);
      match(ExprParser::RIGHTB);
      setState(142);
      match(ExprParser::CIRCUMFLEX);
      setState(159);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case ExprParser::LEFTB: {
          setState(143);
          match(ExprParser::LEFTB);
          setState(144);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->over = add_expr();
          setState(149);
          _errHandler->sync(this);

          _la = _input->LA(1);
          if (_la == ExprParser::COMMA) {
            setState(145);
            match(ExprParser::COMMA);
            setState(146);
            antlrcpp::downCast<Unary_exprContext *>(_localctx)->cond = or_expr();
            empty = false;
          }
          setState(151);
          match(ExprParser::RIGHTB);
          multiChoix1 = 1;
          break;
        }

        case ExprParser::INT: {
          setState(155);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->overSumInt = match(ExprParser::INT);
          multiChoix1 = 2;
          break;
        }

        case ExprParser::IDENT: {
          setState(157);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->overSumI = match(ExprParser::IDENT);
          multiChoix1 = 3;
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(161);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subSum = add_expr();

                  if ((antlrcpp::downCast<Unary_exprContext *>(_localctx)->under->node == nullptr) || (antlrcpp::downCast<Unary_exprContext *>(_localctx)->subSum->node == nullptr))
                      throw std::invalid_argument( "SYNTAX ERROR @ 'BigSUM' RULE" );
                  
                  ExprPtr over;

                  switch (multiChoix1) {
                      case 1: {
                          if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->over->node == nullptr)
                              throw std::invalid_argument( "SYNTAX ERROR @ 'BigSUM' RULE" );
                          over = antlrcpp::downCast<Unary_exprContext *>(_localctx)->over->node; 
                          break;
                      }
                      case 2: {
                          int how = std::stoi((antlrcpp::downCast<Unary_exprContext *>(_localctx)->overSumInt != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->overSumInt->getText() : "")); 
                          if (how > 9) { 
                              throw std::invalid_argument( "ERROR = INT WITH OVER INTEGER > 9 !" );
                          }
                          over = std::make_unique<IntNode>(how); 
                          break;
                          }
                      case 3: {
                          over = std::make_unique<IdentNode>((antlrcpp::downCast<Unary_exprContext *>(_localctx)->overSumI != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->overSumI->getText() : "")[0]);
                          break;
                          }
                      default: throw std::invalid_argument( "ERROR = SUM WITH STRANGE ARGUMENTS (OVER) !" );
                  }

                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node = std::make_shared<BigSumNode>(
                      (antlrcpp::downCast<Unary_exprContext *>(_localctx)->indice != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->indice->getText() : "")[0],
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->under->node,
                      over,
                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subSum->node,
                      empty ? nullptr : antlrcpp::downCast<Unary_exprContext *>(_localctx)->cond->node
                  );

              
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(164);
      match(ExprParser::INTEGRALE);
      setState(165);
      match(ExprParser::UNDERSCORE);
      setState(176);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case ExprParser::LEFTB: {
          setState(166);
          match(ExprParser::LEFTB);
          setState(167);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->underInt = add_expr();
          setState(168);
          match(ExprParser::RIGHTB);
          multiChoix1 = 1;
          break;
        }

        case ExprParser::INT: {
          setState(172);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->underIntINT = match(ExprParser::INT);
          multiChoix1 = 2;
          break;
        }

        case ExprParser::IDENT: {
          setState(174);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->underIntIDENT = match(ExprParser::IDENT);
          multiChoix1 = 3;
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(178);
      match(ExprParser::CIRCUMFLEX);
      setState(189);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case ExprParser::LEFTB: {
          setState(179);
          match(ExprParser::LEFTB);
          setState(180);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->overInt = add_expr();
          setState(181);
          match(ExprParser::RIGHTB);
          multiChoix2 = 1;
          break;
        }

        case ExprParser::INT: {
          setState(185);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->overIntINT = match(ExprParser::INT);
          multiChoix2 = 2;
          break;
        }

        case ExprParser::IDENT: {
          setState(187);
          antlrcpp::downCast<Unary_exprContext *>(_localctx)->overIntIDENT = match(ExprParser::IDENT);
          multiChoix2 = 3;
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(191);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subINT = add_expr();
      setState(192);
      match(ExprParser::DERIVE);
      setState(193);
      match(ExprParser::LEFTB);
      setState(194);
      antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt = match(ExprParser::IDENT);
      setState(195);
      match(ExprParser::RIGHTB);

                  if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->subINT->node == nullptr)
                      throw std::invalid_argument( "SYNTAX ERROR @ 'INTEGRALE' RULE" );

                  ExprPtr a;
                  ExprPtr b;

                  switch (multiChoix1) {
                      case 1: {
                          if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->underInt->node == nullptr)
                              throw std::invalid_argument( "SYNTAX ERROR @ 'INTEGRALE' RULE" );
                           a = antlrcpp::downCast<Unary_exprContext *>(_localctx)->underInt->node;
                           break;
                          }
                      case 2: {
                          int how = std::stoi((antlrcpp::downCast<Unary_exprContext *>(_localctx)->underIntINT != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->underIntINT->getText() : "")); 
                          if (how > 9) { 
                              throw std::invalid_argument( "ERROR = INT WITH UNDER INTEGER > 9 !" );
                          }
                          a = std::make_unique<IntNode>(how); 
                          break;
                          }
                      case 3: {
                          a = std::make_unique<IdentNode>((antlrcpp::downCast<Unary_exprContext *>(_localctx)->underIntIDENT != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->underIntIDENT->getText() : "")[0]);
                          break;
                          }
                      default: throw std::invalid_argument( "ERROR = INTEGRALE WITH STRANGE ARGUMENTS (UNDER) !" );
                  }

                  switch (multiChoix2) {
                      case 1: { 
                          if (antlrcpp::downCast<Unary_exprContext *>(_localctx)->overInt->node == nullptr)
                              throw std::invalid_argument( "SYNTAX ERROR @ 'INTEGRALE' RULE" );
                          b = antlrcpp::downCast<Unary_exprContext *>(_localctx)->overInt->node; 
                          break;
                          }
                      case 2: {
                          int how = std::stoi((antlrcpp::downCast<Unary_exprContext *>(_localctx)->overIntINT != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->overIntINT->getText() : "")); 
                          if (how > 9) { 
                              throw std::invalid_argument( "ERROR = INT WITH OVER INTEGER > 9 !" );
                          }
                          b = std::make_unique<IntNode>(how); 
                          break;
                          }
                      case 3: {
                          b = std::make_unique<IdentNode>((antlrcpp::downCast<Unary_exprContext *>(_localctx)->overIntIDENT != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->overIntIDENT->getText() : "")[0]);
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

                  antlrcpp::downCast<Unary_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
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
                                      antlrcpp::downCast<Unary_exprContext *>(_localctx)->subINT->node, 
                                      (antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt->getText() : "")[0], 
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
                                              antlrcpp::downCast<Unary_exprContext *>(_localctx)->subINT->node, 
                                              (antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt->getText() : "")[0], 
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
                                          antlrcpp::downCast<Unary_exprContext *>(_localctx)->subINT->node, 
                                          (antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt != nullptr ? antlrcpp::downCast<Unary_exprContext *>(_localctx)->varInt->getText() : "")[0], 
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
              
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Mult_exprContext ------------------------------------------------------------------

ExprParser::Mult_exprContext::Mult_exprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExprParser::Unary_exprContext *> ExprParser::Mult_exprContext::unary_expr() {
  return getRuleContexts<ExprParser::Unary_exprContext>();
}

ExprParser::Unary_exprContext* ExprParser::Mult_exprContext::unary_expr(size_t i) {
  return getRuleContext<ExprParser::Unary_exprContext>(i);
}

std::vector<tree::TerminalNode *> ExprParser::Mult_exprContext::IMUL() {
  return getTokens(ExprParser::IMUL);
}

tree::TerminalNode* ExprParser::Mult_exprContext::IMUL(size_t i) {
  return getToken(ExprParser::IMUL, i);
}

std::vector<tree::TerminalNode *> ExprParser::Mult_exprContext::MUL() {
  return getTokens(ExprParser::MUL);
}

tree::TerminalNode* ExprParser::Mult_exprContext::MUL(size_t i) {
  return getToken(ExprParser::MUL, i);
}

std::vector<tree::TerminalNode *> ExprParser::Mult_exprContext::SLASH() {
  return getTokens(ExprParser::SLASH);
}

tree::TerminalNode* ExprParser::Mult_exprContext::SLASH(size_t i) {
  return getToken(ExprParser::SLASH, i);
}


size_t ExprParser::Mult_exprContext::getRuleIndex() const {
  return ExprParser::RuleMult_expr;
}


ExprParser::Mult_exprContext* ExprParser::mult_expr() {
  Mult_exprContext *_localctx = _tracker.createInstance<Mult_exprContext>(_ctx, getState());
  enterRule(_localctx, 6, ExprParser::RuleMult_expr);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(201);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == ExprParser::IMUL) {
      setState(200);
      match(ExprParser::IMUL);
    }
    setState(203);
    antlrcpp::downCast<Mult_exprContext *>(_localctx)->sub = unary_expr();
    setState(208);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(204);
        antlrcpp::downCast<Mult_exprContext *>(_localctx)->_tset605 = _input->LT(1);
        _la = _input->LA(1);
        if (!((((_la & ~ 0x3fULL) == 0) &&
          ((1ULL << _la) & 266242) != 0))) {
          antlrcpp::downCast<Mult_exprContext *>(_localctx)->_tset605 = _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        antlrcpp::downCast<Mult_exprContext *>(_localctx)->op.push_back(antlrcpp::downCast<Mult_exprContext *>(_localctx)->_tset605);
        setState(205);
        antlrcpp::downCast<Mult_exprContext *>(_localctx)->unary_exprContext = unary_expr();
        antlrcpp::downCast<Mult_exprContext *>(_localctx)->mult.push_back(antlrcpp::downCast<Mult_exprContext *>(_localctx)->unary_exprContext); 
      }
      setState(210);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    }

                if ((antlrcpp::downCast<Mult_exprContext *>(_localctx)->sub->node == nullptr) || (validateVector(antlrcpp::downCast<Mult_exprContext *>(_localctx)->mult)))
                    throw std::invalid_argument( "SYNTAX ERROR @ 'MULT' RULE" );

                antlrcpp::downCast<Mult_exprContext *>(_localctx)->node =  antlrcpp::downCast<Mult_exprContext *>(_localctx)->sub->node;
                for (int i = 0; i < antlrcpp::downCast<Mult_exprContext *>(_localctx)->op.size(); ++i) {
                    // si la longueur du texte est > 1 c'est que MUL=\times
                    if (antlrcpp::downCast<Mult_exprContext *>(_localctx)->op[i]->getText().length()>1)
                        antlrcpp::downCast<Mult_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                            "*",
                            _localctx->node,
                            antlrcpp::downCast<Mult_exprContext *>(_localctx)->mult[i]->node
                    );
                    else
                        antlrcpp::downCast<Mult_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                            antlrcpp::downCast<Mult_exprContext *>(_localctx)->op[i]->getText(),
                            _localctx->node,
                            antlrcpp::downCast<Mult_exprContext *>(_localctx)->mult[i]->node
                        );
                }
            
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Add_exprContext ------------------------------------------------------------------

ExprParser::Add_exprContext::Add_exprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExprParser::Mult_exprContext *> ExprParser::Add_exprContext::mult_expr() {
  return getRuleContexts<ExprParser::Mult_exprContext>();
}

ExprParser::Mult_exprContext* ExprParser::Add_exprContext::mult_expr(size_t i) {
  return getRuleContext<ExprParser::Mult_exprContext>(i);
}

std::vector<tree::TerminalNode *> ExprParser::Add_exprContext::ADD() {
  return getTokens(ExprParser::ADD);
}

tree::TerminalNode* ExprParser::Add_exprContext::ADD(size_t i) {
  return getToken(ExprParser::ADD, i);
}

std::vector<tree::TerminalNode *> ExprParser::Add_exprContext::MINUS() {
  return getTokens(ExprParser::MINUS);
}

tree::TerminalNode* ExprParser::Add_exprContext::MINUS(size_t i) {
  return getToken(ExprParser::MINUS, i);
}


size_t ExprParser::Add_exprContext::getRuleIndex() const {
  return ExprParser::RuleAdd_expr;
}


ExprParser::Add_exprContext* ExprParser::add_expr() {
  Add_exprContext *_localctx = _tracker.createInstance<Add_exprContext>(_ctx, getState());
  enterRule(_localctx, 8, ExprParser::RuleAdd_expr);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(213);
    antlrcpp::downCast<Add_exprContext *>(_localctx)->sub = mult_expr();
    setState(218);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(214);
        antlrcpp::downCast<Add_exprContext *>(_localctx)->_tset645 = _input->LT(1);
        _la = _input->LA(1);
        if (!(_la == ExprParser::ADD

        || _la == ExprParser::MINUS)) {
          antlrcpp::downCast<Add_exprContext *>(_localctx)->_tset645 = _errHandler->recoverInline(this);
        }
        else {
          _errHandler->reportMatch(this);
          consume();
        }
        antlrcpp::downCast<Add_exprContext *>(_localctx)->op.push_back(antlrcpp::downCast<Add_exprContext *>(_localctx)->_tset645);
        setState(215);
        antlrcpp::downCast<Add_exprContext *>(_localctx)->mult_exprContext = mult_expr();
        antlrcpp::downCast<Add_exprContext *>(_localctx)->sum.push_back(antlrcpp::downCast<Add_exprContext *>(_localctx)->mult_exprContext); 
      }
      setState(220);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    }

                if ((antlrcpp::downCast<Add_exprContext *>(_localctx)->sub->node == nullptr) || (validateVector(antlrcpp::downCast<Add_exprContext *>(_localctx)->sum)))
                    throw std::invalid_argument( "SYNTAX ERROR @ 'ADD' RULE" );
                
                antlrcpp::downCast<Add_exprContext *>(_localctx)->node =  antlrcpp::downCast<Add_exprContext *>(_localctx)->sub->node;
                for (int i = 0; i < antlrcpp::downCast<Add_exprContext *>(_localctx)->op.size(); ++i) {
                    antlrcpp::downCast<Add_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                        antlrcpp::downCast<Add_exprContext *>(_localctx)->op[i]->getText(),
                        _localctx->node,
                        antlrcpp::downCast<Add_exprContext *>(_localctx)->sum[i]->node
                    );
                }
            
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Primary_boolContext ------------------------------------------------------------------

ExprParser::Primary_boolContext::Primary_boolContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* ExprParser::Primary_boolContext::FALSE() {
  return getToken(ExprParser::FALSE, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::TRUE() {
  return getToken(ExprParser::TRUE, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::IDENT() {
  return getToken(ExprParser::IDENT, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::LEFTPAR() {
  return getToken(ExprParser::LEFTPAR, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::RIGHTPAR() {
  return getToken(ExprParser::RIGHTPAR, 0);
}

ExprParser::Or_exprContext* ExprParser::Primary_boolContext::or_expr() {
  return getRuleContext<ExprParser::Or_exprContext>(0);
}

std::vector<ExprParser::Unary_exprContext *> ExprParser::Primary_boolContext::unary_expr() {
  return getRuleContexts<ExprParser::Unary_exprContext>();
}

ExprParser::Unary_exprContext* ExprParser::Primary_boolContext::unary_expr(size_t i) {
  return getRuleContext<ExprParser::Unary_exprContext>(i);
}

tree::TerminalNode* ExprParser::Primary_boolContext::EQUAL() {
  return getToken(ExprParser::EQUAL, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::LESS() {
  return getToken(ExprParser::LESS, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::GREATER() {
  return getToken(ExprParser::GREATER, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::NotEQUAL() {
  return getToken(ExprParser::NotEQUAL, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::LESSOREQUAL() {
  return getToken(ExprParser::LESSOREQUAL, 0);
}

tree::TerminalNode* ExprParser::Primary_boolContext::GREATEROREQUAL() {
  return getToken(ExprParser::GREATEROREQUAL, 0);
}


size_t ExprParser::Primary_boolContext::getRuleIndex() const {
  return ExprParser::RulePrimary_bool;
}


ExprParser::Primary_boolContext* ExprParser::primary_bool() {
  Primary_boolContext *_localctx = _tracker.createInstance<Primary_boolContext>(_ctx, getState());
  enterRule(_localctx, 10, ExprParser::RulePrimary_bool);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    setState(240);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 15, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(223);
      match(ExprParser::FALSE);
       
                   antlrcpp::downCast<Primary_boolContext *>(_localctx)->node =  std::make_unique<BoolNode>(false);
                  
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(225);
      match(ExprParser::TRUE);
       
                   antlrcpp::downCast<Primary_boolContext *>(_localctx)->node =  std::make_unique<BoolNode>(true);
                  
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(227);
      antlrcpp::downCast<Primary_boolContext *>(_localctx)->identToken = match(ExprParser::IDENT);
       
                   antlrcpp::downCast<Primary_boolContext *>(_localctx)->node =  std::make_unique<IdentNode>((antlrcpp::downCast<Primary_boolContext *>(_localctx)->identToken != nullptr ? antlrcpp::downCast<Primary_boolContext *>(_localctx)->identToken->getText() : "")[0]);
                  
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(229);
      match(ExprParser::LEFTPAR);
      setState(230);
      antlrcpp::downCast<Primary_boolContext *>(_localctx)->e = or_expr();
      setState(231);
      match(ExprParser::RIGHTPAR);
       
              antlrcpp::downCast<Primary_boolContext *>(_localctx)->node =  antlrcpp::downCast<Primary_boolContext *>(_localctx)->e->node; 
             
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(234);
      antlrcpp::downCast<Primary_boolContext *>(_localctx)->primLeft = unary_expr();

      setState(235);
      antlrcpp::downCast<Primary_boolContext *>(_localctx)->_tset722 = _input->LT(1);
      _la = _input->LA(1);
      if (!((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & 33030144) != 0))) {
        antlrcpp::downCast<Primary_boolContext *>(_localctx)->_tset722 = _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      antlrcpp::downCast<Primary_boolContext *>(_localctx)->op.push_back(antlrcpp::downCast<Primary_boolContext *>(_localctx)->_tset722);
      setState(236);
      antlrcpp::downCast<Primary_boolContext *>(_localctx)->primRight = unary_expr();

                  antlrcpp::downCast<Primary_boolContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                      antlrcpp::downCast<Primary_boolContext *>(_localctx)->op[0]->getText(),
                      antlrcpp::downCast<Primary_boolContext *>(_localctx)->primLeft->node,
                      antlrcpp::downCast<Primary_boolContext *>(_localctx)->primRight->node
                  );
              
      break;
    }

    default:
      break;
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Unary_boolContext ------------------------------------------------------------------

ExprParser::Unary_boolContext::Unary_boolContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

ExprParser::Primary_boolContext* ExprParser::Unary_boolContext::primary_bool() {
  return getRuleContext<ExprParser::Primary_boolContext>(0);
}

tree::TerminalNode* ExprParser::Unary_boolContext::BoolNOT() {
  return getToken(ExprParser::BoolNOT, 0);
}


size_t ExprParser::Unary_boolContext::getRuleIndex() const {
  return ExprParser::RuleUnary_bool;
}


ExprParser::Unary_boolContext* ExprParser::unary_bool() {
  Unary_boolContext *_localctx = _tracker.createInstance<Unary_boolContext>(_ctx, getState());
  enterRule(_localctx, 12, ExprParser::RuleUnary_bool);
  bool empty = true;
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(244);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == ExprParser::BoolNOT) {
      setState(242);
      antlrcpp::downCast<Unary_boolContext *>(_localctx)->boolnotToken = match(ExprParser::BoolNOT);
      antlrcpp::downCast<Unary_boolContext *>(_localctx)->opS.push_back(antlrcpp::downCast<Unary_boolContext *>(_localctx)->boolnotToken);
      empty = false;
    }
    setState(246);
    antlrcpp::downCast<Unary_boolContext *>(_localctx)->primS = primary_bool();
     
                if (antlrcpp::downCast<Unary_boolContext *>(_localctx)->primS->node == nullptr)
                    throw std::invalid_argument( "SYNTAX ERROR @ '\\neg prim' RULE" );
                
                // if no unary_operator
                if (empty)
                        antlrcpp::downCast<Unary_boolContext *>(_localctx)->node = antlrcpp::downCast<Unary_boolContext *>(_localctx)->primS->node;
                else 
                    antlrcpp::downCast<Unary_boolContext *>(_localctx)->node =  std::make_shared<UnaryOpNode>("NOT",antlrcpp::downCast<Unary_boolContext *>(_localctx)->primS->node);
            
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- And_exprContext ------------------------------------------------------------------

ExprParser::And_exprContext::And_exprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExprParser::Unary_boolContext *> ExprParser::And_exprContext::unary_bool() {
  return getRuleContexts<ExprParser::Unary_boolContext>();
}

ExprParser::Unary_boolContext* ExprParser::And_exprContext::unary_bool(size_t i) {
  return getRuleContext<ExprParser::Unary_boolContext>(i);
}

std::vector<tree::TerminalNode *> ExprParser::And_exprContext::BoolAND() {
  return getTokens(ExprParser::BoolAND);
}

tree::TerminalNode* ExprParser::And_exprContext::BoolAND(size_t i) {
  return getToken(ExprParser::BoolAND, i);
}


size_t ExprParser::And_exprContext::getRuleIndex() const {
  return ExprParser::RuleAnd_expr;
}


ExprParser::And_exprContext* ExprParser::and_expr() {
  And_exprContext *_localctx = _tracker.createInstance<And_exprContext>(_ctx, getState());
  enterRule(_localctx, 14, ExprParser::RuleAnd_expr);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(249);
    antlrcpp::downCast<And_exprContext *>(_localctx)->sub = unary_bool();
    setState(254);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == ExprParser::BoolAND) {
      setState(250);
      antlrcpp::downCast<And_exprContext *>(_localctx)->boolandToken = match(ExprParser::BoolAND);
      antlrcpp::downCast<And_exprContext *>(_localctx)->op.push_back(antlrcpp::downCast<And_exprContext *>(_localctx)->boolandToken);
      setState(251);
      antlrcpp::downCast<And_exprContext *>(_localctx)->unary_boolContext = unary_bool();
      antlrcpp::downCast<And_exprContext *>(_localctx)->sum.push_back(antlrcpp::downCast<And_exprContext *>(_localctx)->unary_boolContext);
      setState(256);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }

                if ((antlrcpp::downCast<And_exprContext *>(_localctx)->sub->node == nullptr) || (validateVector(antlrcpp::downCast<And_exprContext *>(_localctx)->sum)))
                    throw std::invalid_argument( "SYNTAX ERROR @ 'AND' RULE" );
              
                antlrcpp::downCast<And_exprContext *>(_localctx)->node =  antlrcpp::downCast<And_exprContext *>(_localctx)->sub->node;
                for (int i = 0; i < antlrcpp::downCast<And_exprContext *>(_localctx)->op.size(); ++i) {
                    antlrcpp::downCast<And_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                        "AND",
                        _localctx->node,
                        antlrcpp::downCast<And_exprContext *>(_localctx)->sum[i]->node
                    );
                }
            
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Or_exprContext ------------------------------------------------------------------

ExprParser::Or_exprContext::Or_exprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<ExprParser::And_exprContext *> ExprParser::Or_exprContext::and_expr() {
  return getRuleContexts<ExprParser::And_exprContext>();
}

ExprParser::And_exprContext* ExprParser::Or_exprContext::and_expr(size_t i) {
  return getRuleContext<ExprParser::And_exprContext>(i);
}

std::vector<tree::TerminalNode *> ExprParser::Or_exprContext::BoolOR() {
  return getTokens(ExprParser::BoolOR);
}

tree::TerminalNode* ExprParser::Or_exprContext::BoolOR(size_t i) {
  return getToken(ExprParser::BoolOR, i);
}


size_t ExprParser::Or_exprContext::getRuleIndex() const {
  return ExprParser::RuleOr_expr;
}


ExprParser::Or_exprContext* ExprParser::or_expr() {
  Or_exprContext *_localctx = _tracker.createInstance<Or_exprContext>(_ctx, getState());
  enterRule(_localctx, 16, ExprParser::RuleOr_expr);
  size_t _la = 0;

#if __cplusplus > 201703L
  auto onExit = finally([=, this] {
#else
  auto onExit = finally([=] {
#endif
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(259);
    antlrcpp::downCast<Or_exprContext *>(_localctx)->sub = and_expr();
    setState(264);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == ExprParser::BoolOR) {
      setState(260);
      antlrcpp::downCast<Or_exprContext *>(_localctx)->boolorToken = match(ExprParser::BoolOR);
      antlrcpp::downCast<Or_exprContext *>(_localctx)->op.push_back(antlrcpp::downCast<Or_exprContext *>(_localctx)->boolorToken);
      setState(261);
      antlrcpp::downCast<Or_exprContext *>(_localctx)->and_exprContext = and_expr();
      antlrcpp::downCast<Or_exprContext *>(_localctx)->sum.push_back(antlrcpp::downCast<Or_exprContext *>(_localctx)->and_exprContext);
      setState(266);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }

                if ((antlrcpp::downCast<Or_exprContext *>(_localctx)->sub->node == nullptr) || (validateVector(antlrcpp::downCast<Or_exprContext *>(_localctx)->sum)))
                    throw std::invalid_argument( "SYNTAX ERROR @ 'OR' RULE" );
             
                antlrcpp::downCast<Or_exprContext *>(_localctx)->node =  antlrcpp::downCast<Or_exprContext *>(_localctx)->sub->node;
                for (int i = 0; i < antlrcpp::downCast<Or_exprContext *>(_localctx)->op.size(); ++i) {
                    antlrcpp::downCast<Or_exprContext *>(_localctx)->node =  std::make_shared<BinaryOpNode>(
                        "OR",
                        _localctx->node,
                        antlrcpp::downCast<Or_exprContext *>(_localctx)->sum[i]->node
                    );
                }
            
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

void ExprParser::initialize() {
#if ANTLR4_USE_THREAD_LOCAL_CACHE
  exprparserParserInitialize();
#else
  ::antlr4::internal::call_once(exprparserParserOnceFlag, exprparserParserInitialize);
#endif
}
