#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"


#include "clang/Driver/Options.h" 
#include "clang/AST/AST.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"

#include <sstream>
#include <unordered_set>

using namespace clang::tooling;
using namespace clang::driver;
using namespace clang;
using namespace llvm;


std::stringstream os;
std::map<std::string, int> UID_map;
std::map<int, std::string> UID_inv_map;
std::map<int, int> UID_size_map;

std::map<int, std::map<std::string, int>> field_map;

void generateFixedCode(void) {
	os << "var $M.int : [int] int;" << std::endl;
	os << "var $M._size : [int] int;" << std::endl;
	os << "var $M._type : [int] int;" << std::endl;
	os << "var $M._C : [int] int;" << std::endl;
	os << "var $currAddr : int;" << std::endl;

	//malloc procedure
	os << "procedure $malloc(n:int) returns (p:int) {" << std::endl;
	os << "\tp := $currAddr;" << std::endl;
	os << "\t$currAddr := $currAddr + n;" << std::endl;
	os << "}" << std::endl;

	//malloc_int procedure
	os << "procedure malloc_int(n:int) returns (p:int) {" << std::endl;
	os << "\tcall p := $malloc(n*4);" << std::endl;
	os << "\t$M._type[p] := 0;" << std::endl;
	os << "\t$M._size[p] := n;" << std::endl;
	os << "}" << std::endl;

	//cast void procedure
	os << "procedure $cast_void(p:int) returns (q:int) {" << std::endl;
	os << "\tq := p;" << std::endl;
	os << "}" << std::endl;
}

const QualType getBaseType(QualType t) {
	if (const ElaboratedType *ET = dyn_cast<ElaboratedType>(t.getTypePtr())) {
		return getBaseType(ET->getNamedType());
	}
	else if (const TypedefType *TD = dyn_cast<TypedefType>(t.getTypePtr())) {
		return getBaseType(TD->getDecl()->getUnderlyingType());
	}
	else
		return t;
}

class CollectStructInfoVisitor : public RecursiveASTVisitor<CollectStructInfoVisitor> {
private:
	ASTContext *Context;
	int UID;
public:
	
	bool VisitRecordDecl(RecordDecl *R) {
		UID_map[R->getName().str()] = UID;
		UID_inv_map[UID] = R->getName().str();
		int count = 0;
		for (RecordDecl::field_iterator f = R->field_begin(); f != R->field_end(); f++) {
			field_map[UID][(*f)->getName()] = count;
			const QualType t = getBaseType((*f)->getType());
			if (t->isStructureType()) {
				count += UID_size_map[UID_map[(*f)->getType()->getAsStructureType()->getDecl()->getName().str()]];
			}
			else if (t->isCharType()) {
				count += 1;
			}
			else {
				count += 4;
			}
		}
		UID_size_map[UID] = count;
		UID++;
		return true;
	}
	explicit CollectStructInfoVisitor(ASTContext *Context) : Context(Context), UID(1) {}
};
class CreateStructDefsVisitor : public RecursiveASTVisitor<CreateStructDefsVisitor> {
private:
	ASTContext *Context;
public:
	bool VisitRecordDecl(RecordDecl *R) {
		int UID = UID_map[R->getName().str()];
		os << "// UID(" << R->getName().str() << ") = "<<UID<<std::endl;
		for (RecordDecl::field_iterator f = R->field_begin(); f != R->field_end(); f++) {
			os << "var $M." << R->getName().str() << "." << f->getName().str() << " : [int] int" << std::endl;
		}
		// struct malloc
		os << "procedure malloc_" << R->getName().str() << "(n:int) returns (p:int) {" << std::endl;
		os << "\tcall p := $malloc(n*" << UID_size_map[UID] << ");" << std::endl;
		os << "\t$M._type[p] := " << UID << ";" << std::endl;
		os << "\t$M._size[p] := n;" << std::endl;
		os << "}" << std::endl;

		//struct cast 
		os << "procedure $cast_" << R->getName().str() << "(p:int) returns (q:int) {" << std::endl;
		os << "\tassert $M._C[" << UID << "][$M._type[p]] == 1;" << std::endl;
		os << "\tq := p;" << std::endl;
		os << "}" << std::endl;
		return true;
	}
	explicit CreateStructDefsVisitor(ASTContext *Context) : Context(Context) {}
};

class CreateFunctionDefinitionsVisitor : public RecursiveASTVisitor<CreateFunctionDefinitionsVisitor> {
private:
	ASTContext *Context;
	int tempCount = 0;
	std::stringstream fs;
	std::map<int, std::map<std::string, std::string>> symbolTable;
	int symbolTableLevel=0;
	std::unordered_set<std::string> varList;
	void symbolTableEnterLevel(void) {
		symbolTableLevel++;
		std::map<std::string, std::string> table;
		symbolTable[symbolTableLevel] = table;
	}
	void symbolTableExitLevel(void) {
		symbolTable.erase(symbolTableLevel);
		symbolTableLevel--;
	}
	void symbolTableCreateVar(std::string var) {
		std::stringstream ss;
		ss << var << "$" << symbolTableLevel;
		symbolTable[symbolTableLevel][var] = ss.str();
	}
	std::string symbolTableGetVar(std::string var) {
		for (int i = symbolTableLevel; i >= 0; i--) {
			if (symbolTable[i].find(var) != symbolTable[i].end())
				return symbolTable[i][var];
		}
		return var;
	}
	int getNextTemp() {
		int t = tempCount;
		tempCount++;
		return t;
	}
	void resetTemp() {
		tempCount = 0;
	}
	std::string getAsTemp(int n) {
		std::stringstream s;
		s << "$temp_" << n;
		return s.str();
	}
	void generateTabs(int n) {
		for (int i = 0; i < n; i++)
			fs << "\t";
	}
	std::string nTabs(int n) {
		std::stringstream s;
		for (int i = 0; i < n; i++)
			s << "\t";
		return s.str();
	}
	std::string getTemporaryDeclarations() {
		std::stringstream s;
		for (int i = 0; i < tempCount; i++) {
			s << "\t" << "var " << getAsTemp(i) << " : int;" << std::endl;
		}
		return s.str();
	}
	int generateStructCopy(QualType t, int lhs_base, int rhs_base, int base_offset, int indent ) {
		RecordDecl *RD = t->getAsStructureType()->getDecl();
		for (RecordDecl::field_iterator f = RD->field_begin(); f != RD->field_end(); f++) {
			const QualType t = getBaseType((*f)->getType());
			std::string l_type = RD->getName().str();
			int offset = field_map[UID_map[l_type]][(*f)->getName().str()];
			if (t->isStructureType()) {
				generateStructCopy((*f)->getType(), lhs_base, rhs_base, offset, indent);
			}
			else {
				fs << nTabs(indent) << "$M." << l_type << "." << (*f)->getName().str() << "[" << getAsTemp(lhs_base) << " + " << offset + base_offset << "] = $M." << l_type << "." << (*f)->getName().str() << "[" << getAsTemp(rhs_base) << " + " << offset + base_offset << "];" << std::endl;
			}
		}
		return rhs_base;
	}
	int getElementPtr(Expr *E, int indent) {
		if (CastExpr *CE = dyn_cast<CastExpr>(E)) {
			return getElementPtr(CE->getSubExpr(), indent);
		}
		else if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
			Expr *base = ME->getBase();
			int b;
			std::string l_type;
			int t = getNextTemp();
			if (ME->isArrow()) {
				b = generateStatement(base, indent);
				l_type = base->getType()->getPointeeType()->getAsStructureType()->getDecl()->getName().str();
			}
			else {
				b = getElementPtr(base, indent);
				l_type = base->getType()->getAsStructureType()->getDecl()->getName().str();
			}
			int offset = field_map[UID_map[l_type]][ME->getMemberDecl()->getName().str()];
			fs << nTabs(indent) << getAsTemp(t) << " := " << getAsTemp(b) << " + " << offset << ";" << std::endl;
			return t;
		}
		else if(UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
			if (UO->getOpcodeStr(UO->getOpcode()).str().compare("*") == 0) {
				return generateStatement(UO->getSubExpr(),indent);
			}
			else {
				fs << nTabs(indent) << "// Invalid operator found in getelementptr" << std::endl;
				return -1;
			}
		}
		else if (DeclRefExpr *DE = dyn_cast<DeclRefExpr>(E)) {
			return generateStatement(DE, indent);
		}
		else {
		//	E->dump();
			fs << nTabs(indent) << "// Invalid expression found in getelementptr" << std::endl;
			return -1;
		}
		return -1;
	}
	std::string getLValue(Expr *E, int indent) {
		if (DeclRefExpr *DE = dyn_cast<DeclRefExpr>(E)) {
			return symbolTableGetVar(DE->getDecl()->getName().str());
		}
		else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
			if (UO->getOpcodeStr(UO->getOpcode()).str().compare("*") == 0) {
				int t = generateStatement(UO->getSubExpr(), indent);
				std::stringstream ss;
				ss << "$M.[" << getAsTemp(t) << "]";
				return ss.str();
			}
			else {
				fs << nTabs(indent) << "// Invalid unary operator found in getlvalue" << std::endl;
				return getAsTemp(-1);
			}
		}
		else if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
			Expr *base = ME->getBase();
			int b;
			std::string l_type;
			if (ME->isArrow()) {
				b = generateStatement(base, indent);
				l_type = base->getType()->getPointeeType()->getAsStructureType()->getDecl()->getName().str();
			}
			else {
				b = getElementPtr(base, indent);
				l_type = base->getType()->getAsStructureType()->getDecl()->getName().str();
			}
			int offset = field_map[UID_map[l_type]][ME->getMemberDecl()->getName().str()];
			std::stringstream ss;
			ss << "$M." << l_type << "." << ME->getMemberDecl()->getName().str() << "[" << getAsTemp(b) << " + " << offset << "]";
			return ss.str();
		}
		else {
			fs << nTabs(indent) << "//Invalid lvalue found" << std::endl;
			return getAsTemp(-1);
		}
	}
	int generateStatement(Stmt *S, int indent) {
		if (CompoundStmt *CS = dyn_cast<CompoundStmt>(S)) {
			int t=-1;
			symbolTableEnterLevel();
			for (CompoundStmt::body_iterator b = CS->body_begin(); b != CS->body_end(); b++) {
				t=generateStatement(*b, indent);
			}
			symbolTableExitLevel();
			return t;
		}
		else if (Expr *E = dyn_cast<Expr>(S)) {
			if (IntegerLiteral *I = dyn_cast<IntegerLiteral>(E)) {
				int t = getNextTemp();
				fs << nTabs(indent) << getAsTemp(t) << " := " << I->getValue().getSExtValue() << ";" << std::endl;
				return t;
			}
			else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
				if (BO->getOpcodeStr().str().compare("=") == 0) {
					if (BO->getRHS()->getType()->isStructureType()) {
						int lhs_base = getElementPtr(BO->getLHS(), indent);
						int rhs_base = getElementPtr(BO->getRHS(), indent);
						return generateStructCopy(BO->getRHS()->getType(), lhs_base, rhs_base, 0, indent);
					}
					else {
						std::string lvalue = getLValue(BO->getLHS(), indent);
						int t = generateStatement(BO->getRHS(), indent);
						fs << nTabs(indent) << lvalue << " := " << getAsTemp(t) << ";" << std::endl;
						return t;
					}
				}
				int lhs = generateStatement(BO->getLHS(), indent);
				int rhs = generateStatement(BO->getRHS(), indent);
				int t = getNextTemp();
				fs << nTabs(indent) << getAsTemp(t) << " := " << getAsTemp(lhs) << " " << BO->getOpcodeStr().str() << " " << getAsTemp(rhs) << ";" << std::endl;
				return t;
			}
			else if (CastExpr *CE = dyn_cast<CastExpr>(E)) {
				return generateStatement(CE->getSubExpr(), indent);
			}
			else if (CharacterLiteral *CL = dyn_cast<CharacterLiteral>(E)) {
				int t = getNextTemp();
				fs << nTabs(indent) << getAsTemp(t) << " := " << CL->getValue() << ";" << std::endl;
				return t;
			}
			else if (AbstractConditionalOperator *CE = dyn_cast<AbstractConditionalOperator>(E)) {
				int c = generateStatement(CE->getCond(), indent);
				int f = getNextTemp();
				int t;
				fs << nTabs(indent) << "if ( " << getAsTemp(c) << " != 0 ) {" << std::endl;
				t = generateStatement(CE->getTrueExpr(), indent + 1);
				fs << nTabs(indent + 1) << getAsTemp(f) << " := " << getAsTemp(t) << ";" << std::endl;
				fs << nTabs(indent) << "} else {" << std::endl;
				t = generateStatement(CE->getFalseExpr(), indent + 1);
				fs << nTabs(indent + 1) << getAsTemp(f) << " := " << getAsTemp(t) << ";" << std::endl;
				fs << nTabs(indent) << "}" << std::endl;
				return f;
			}
			else if (DeclRefExpr *DE = dyn_cast<DeclRefExpr>(E)) {
				int t = getNextTemp();
				fs << nTabs(indent) << getAsTemp(t) << " := " << symbolTableGetVar(DE->getDecl()->getName().str()) << ";" << std::endl;
				return t;
			}
			else if (StmtExpr *SE = dyn_cast<StmtExpr>(E)) {
				return generateStatement(SE->getSubStmt(), indent);                   
			}
			else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
				//fs << nTabs(indent) << "// Unary operator " << UO->getOpcodeStr(UO->getOpcode()).str() << std::endl;
				if (UO->getOpcodeStr(UO->getOpcode()).str().compare("-")==0) {
					int t = generateStatement(UO->getSubExpr(),indent);
					fs << nTabs(indent) << getAsTemp(t) << " := 0 - " << getAsTemp(t) << ";" << std::endl;
					return t;
				}
				else if (UO->getOpcodeStr(UO->getOpcode()).str().compare("!")==0) {
					int t = generateStatement(UO->getSubExpr(), indent);
					fs << nTabs(indent) << "if ( " << getAsTemp(t) << " == 0 )" << std::endl;
					fs << nTabs(indent + 1) << getAsTemp(t) << " := 1;" << std::endl;
					fs << nTabs(indent) << "else" << std::endl;
					fs << nTabs(indent + 1) << getAsTemp(t) << " := 0;" << std::endl;
					return(t);
				}
				else if (UO->getOpcodeStr(UO->getOpcode()).str().compare("*")==0) {
					int t = generateStatement(UO->getSubExpr(), indent);
					fs << nTabs(indent) << getAsTemp(t) << " := $M.int[" << getAsTemp(t) << "];" << std::endl;
					return(t);
				}
				else {
					fs << nTabs(indent) << "//Unary Operator Not Handled yet!" << std::endl;
					return -1;
				}
			}
			else if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
				std::string fname;
				Expr *callee = CE->getCallee();
				CastExpr *CastE = dyn_cast<CastExpr>(callee);
				if (CastE == NULL) {
					fs << nTabs(indent) << "// function call of this type not handled" << std::endl;
					return -1;
				}
				DeclRefExpr *func = dyn_cast<DeclRefExpr>(CastE->getSubExpr());
				if (func == NULL) {
					fs << nTabs(indent) << "// function call of this type not handled" << std::endl;
					return -1;
				}
				FunctionDecl *fdecl = dyn_cast<FunctionDecl>(func->getFoundDecl());
				if (fdecl == NULL) {
					fs << nTabs(indent) << "// function call of this type not handled" << std::endl;
					return -1;
				}
				fname = fdecl->getName().str();
				int *args = new int[CE->getNumArgs()];
				Expr **argvs = CE->getArgs();
				for (unsigned int i = 0; i < CE->getNumArgs(); i++) {
					args[i] = generateStatement(argvs[i], indent);
				}
				int t = getNextTemp();
				fs << nTabs(indent) << "call " << getAsTemp(t) << " := " << fname << "(";
				for (unsigned int i = 0; i < CE->getNumArgs(); i++) {
					fs << getAsTemp(args[i]);
					if (i != CE->getNumArgs() - 1)
						fs << ", ";
				}
				fs << ");" << std::endl;
				delete[] args;
				return -1;
			}
			else if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
				Expr *base = ME->getBase();
				int b;
				
				int t = getNextTemp();
				std::string l_type;
				if (ME->isArrow()) {
					l_type = base->getType()->getPointeeType()->getAsStructureType()->getDecl()->getName().str();
					b = generateStatement(base, indent);
				}
				else {
					b = getElementPtr(base, indent);
					l_type = base->getType()->getAsStructureType()->getDecl()->getName().str();
				}
				int offset = field_map[UID_map[l_type]][ME->getMemberDecl()->getName().str()];
				fs << nTabs(indent) << getAsTemp(t) << " := $M." << l_type << "." << ME->getMemberDecl()->getName().str() << "[" << getAsTemp(b) << " + " << offset << "];" << std::endl;
				return t;
			}
			else {
				generateTabs(indent);
				fs << "//Expr Not Handled yet!"<<std::endl;
				return -1;
			}
		}
		else if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
			int t = generateStatement(RS->getRetValue(), indent);
			fs << nTabs(indent) << "$return := " << getAsTemp(t) << ";" << std::endl;
			fs << nTabs(indent) << "return;" << std::endl;
			return t;
		}
		else if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
			for (DeclStmt::decl_iterator d = DS->decl_begin(); d != DS->decl_end(); d++) {
				if (VarDecl *VD = dyn_cast<VarDecl>(*d)) {
					symbolTableCreateVar(VD->getName().str());
					varList.insert(symbolTableGetVar(VD->getName().str()));
					fs << nTabs(indent) << "havoc " << symbolTableGetVar(VD->getName().str()) << ";" << std::endl;
					if (VD->getType()->isStructureType()) {
						std::string sname = VD->getType()->getAsStructureType()->getDecl()->getName().str();
						fs << nTabs(indent) << symbolTableGetVar(VD->getName().str()) << " := $malloc_" << sname << "(1);" << std::endl;
					}
					if (VD->hasInit()) {
						if (VD->getType()->isStructureType()) {
							int rhs_base = getElementPtr(VD->getInit(), indent);
							int lhs_base = getNextTemp();
							fs << nTabs(indent) << getAsTemp(lhs_base) << " := " << symbolTableGetVar(VD->getName().str()) << ";" << std::endl;
							generateStructCopy(VD->getType(), lhs_base, rhs_base, 0, indent);
						}
						else {
							int t = generateStatement(VD->getInit(), indent);
							fs << nTabs(indent) << symbolTableGetVar(VD->getName().str()) << " := " << getAsTemp(t) << ";" << std::endl;
						}
					}
				}
				
			}
			return -1;
		}
		else {
			generateTabs(indent);
			fs << "//Stmt Not Handled yet!"<<std::endl;
			return -1;
		}
	}
public:
	bool VisitFunctionDecl(FunctionDecl *F) {
		if (!F->isThisDeclarationADefinition())
			return true;
		os << "// procedure "<< F->getName().str()<<std::endl;
		symbolTableEnterLevel();
		varList.clear();
		os << "procedure " << F->getName().str() << "(";
		fs.str(std::string());
		resetTemp();
		for (FunctionDecl::param_iterator p = F->param_begin(); p != F->param_end(); p++) {
			if ((*p)->getType()->isStructureType()) {
				os << (*p)->getName().str() << "$ptr" << " : int";
				int lhs_base = getNextTemp();
				int rhs_base = getNextTemp();
				fs << "\t" << getAsTemp(lhs_base) << " := " << (*p)->getName().str() << "$ptr;" << std::endl;
				symbolTableCreateVar((*p)->getName().str());
				fs << "\t" << "havoc " << symbolTableGetVar((*p)->getName().str()) << ";" << std::endl;
				fs << "\t" << symbolTableGetVar((*p)->getName().str()) << " := $malloc_" << (*p)->getType()->getAsStructureType()->getDecl()->getName().str() << "(1);" << std::endl;
				fs << "\t" << getAsTemp(rhs_base) << " := " << symbolTableGetVar((*p)->getName().str()) << ";" << std::endl;
				generateStructCopy((*p)->getType(), lhs_base, rhs_base, 0, 1);
			}
			else {
				symbolTableCreateVar((*p)->getName().str());
				os << symbolTableGetVar((*p)->getName().str()) << " : int";
			}
			
			if (p + 1 != F->param_end())
				os << ", ";
		}
		os << ") returns ($return : int) {" << std::endl;
		
		
		generateStatement(F->getBody(),1);
		for (std::unordered_set<std::string>::iterator var = varList.begin(); var != varList.end(); var++)
			os << "\t" << "var " << *var << " : int;" << std::endl;
		os << getTemporaryDeclarations();
		os << fs.str();
		os << "}";
		symbolTableExitLevel();
		return true;
	}
	explicit CreateFunctionDefinitionsVisitor(ASTContext *Context) : Context(Context) {}
};

class BoogieGenConsumer : public clang::ASTConsumer {
private:
	CollectStructInfoVisitor Visitor1;
	CreateStructDefsVisitor Visitor2;
	CreateFunctionDefinitionsVisitor Visitor3;
	
public:
	virtual void HandleTranslationUnit(clang::ASTContext &Context) {
		generateFixedCode();
		Visitor1.TraverseDecl(Context.getTranslationUnitDecl());
		Visitor2.TraverseDecl(Context.getTranslationUnitDecl());
		Visitor3.TraverseDecl(Context.getTranslationUnitDecl());
	}
	explicit BoogieGenConsumer(ASTContext *Context) : Visitor1(Context), Visitor2(Context), Visitor3(Context) {}
};

class BoogieGenAction : public clang::ASTFrontendAction {
public:
	
	virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
		clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
		return std::unique_ptr<clang::ASTConsumer>(
			new BoogieGenConsumer(&Compiler.getASTContext()));
	}
};

static llvm::cl::OptionCategory BoogieGenCategory("boogie-gen options");

int main(int argc, const char **argv) {
	if (argc > 1) {
		CommonOptionsParser OptionsParser(argc, argv, BoogieGenCategory);
		ClangTool Tool(OptionsParser.getCompilations(), OptionsParser.getSourcePathList());
		Tool.run(newFrontendActionFactory<BoogieGenAction>().get());
		errs() << os.str();
		return 0;
	}
}
