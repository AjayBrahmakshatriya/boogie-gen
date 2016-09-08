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
#include <fstream>

using namespace clang::tooling;
using namespace clang::driver;
using namespace clang;
using namespace llvm;


std::stringstream os;
std::set<VarDecl*> globalInits;
std::map<std::string, int> UID_map;
std::map<int, std::string> UID_inv_map;
std::map<int, int> UID_size_map;

std::map<int, std::map<std::string, int>> field_map;

void generateFixedCode(void) {
	os << "var $M.int : [int] int;" << std::endl;
	os << "var $M.char : [int] int;" << std::endl;
	os << "var $M._size : [int] int;" << std::endl;
	os << "var $M._type : [int] int;" << std::endl;
	os << "var $M._C : [int] [int] int;" << std::endl;
	os << "var $M._alloc : [int] int;" << std::endl;
	os << "var $M._typesize : [int] int;" << std::endl;
	os << "var $currAddr : int;" << std::endl;

	//malloc procedure
	os << "procedure $malloc(n:int) returns (p:int) {" << std::endl;
	os << "\tp := $currAddr;" << std::endl;
	os << "\t$M._alloc[p] := 1;" << std::endl;
	os << "\t$currAddr := $currAddr + n;" << std::endl;
	os << "}" << std::endl;

	//malloc_int procedure
	os << "procedure malloc_int(n:int) returns (p:int) {" << std::endl;
	os << "\tcall p := $malloc(n*4);" << std::endl;
	os << "\t$M._type[p] := 0;" << std::endl;
	os << "\t$M._size[p] := n;" << std::endl;
	os << "}" << std::endl;

	//malloc_char procedure
	os << "procedure malloc_char(n:int) returns (p:int) {" << std::endl;
	os << "\tcall p := $malloc(n*4);" << std::endl;
	os << "\t$M._type[p] := 1;" << std::endl;
	os << "\t$M._size[p] := n;" << std::endl;
	os << "}" << std::endl;

	//cast void procedure
	os << "procedure $cast_void(p:int) returns (q:int) {" << std::endl;
	os << "\tq := p;" << std::endl;
	os << "}" << std::endl;

	//cast int procedure
	os << "procedure $cast_int(p:int) returns (q:int) {" << std::endl;
	os << "\tassert p == 0 || $M._alloc[p] == 1;" << std::endl;
	os << "\tassert p == 0 || $M._C[0][$M._type[p]] == 1;" << std::endl;
	os << "\tassert p == 0 || $M._size[p] == 1;" << std::endl;
	os << "\tq := p;" << std::endl;
	os << "}" << std::endl;

	//cast char procedure
	os << "procedure $cast_char(p:int) returns (q:int) {" << std::endl;
	os << "\tassert p == 0 || $M._alloc[p] == 1;" << std::endl;
	os << "\tassert p == 0 || $M._C[1][$M._type[p]] == 1;" << std::endl;
	os << "\tassert p == 0 || $M._size[p] == 1;" << std::endl;
	os << "\tq := p;" << std::endl;
	os << "}" << std::endl;

	//bool_to_int procedure
	os << "procedure $bool_to_int(p:bool) returns (q:int) {" << std::endl;
	os << "\tif (p) {" << std::endl;
	os << "\t\tq := 1;" << std::endl;
	os << "\t} else {" << std::endl;
	os << "\t\tq := 0;" << std::endl;
	os << "\t}" << std::endl;
	os << "\t return;" << std::endl;
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

bool compileCheckErrored = false;

class CompileChecksVisitor : public RecursiveASTVisitor<CompileChecksVisitor> {
private:
	ASTContext *Context;
public:
	explicit CompileChecksVisitor(ASTContext *Context) : Context(Context) {}
	
	bool VisitStmt(Stmt *E) {
		if (CastExpr *CE = dyn_cast<CastExpr>(E)) {
			if (CE->getCastKind() == CK_LValueToRValue || CE->getCastKind() == CK_FunctionToPointerDecay)
				return true;
			if (CE->getType()->isPointerType()) {
				if (!CE->getSubExpr()->getType()->isPointerType()) {
					if (IntegerLiteral *IL = dyn_cast<IntegerLiteral>(CE->getSubExpr())) {
						if (IL->getValue().getSExtValue() == 0)
							return true;
					}
					if (CE->getSubExpr()->getType()->isArrayType() && CE->getSubExpr()->getType()->getArrayElementTypeNoTypeQual()->isCharType() && CE->getType()->getPointeeType()->isCharType()) {
						return true;
					}
					errs() << CE->getLocStart().printToString(Context->getSourceManager()) << " : Error" << " : Only pointers can be casted to pointers. Attempted casting " << CE->getSubExpr()->getType().getAsString() << " to " << CE->getType().getAsString() << ".\n";
					compileCheckErrored = true;
				}
			}
		}
		else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
			if (BO->getOpcodeStr().compare("+") == 0 || BO->getOpcodeStr().compare("-") == 0 || BO->getOpcodeStr().compare("/") == 0 || BO->getOpcodeStr().compare("*") == 0 || BO->getOpcodeStr().compare("&") == 0 || BO->getOpcodeStr().compare("|") == 0) {
				if (BO->getLHS()->getType()->isPointerType() || BO->getRHS()->getType()->isPointerType()) {
					errs() << BO->getLocStart().printToString(Context->getSourceManager()) << " : Error" << " : Cant perform arithmetic operations on pointers. Prohibited.\n";
					compileCheckErrored = true;
				}
			}
		}
		else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
			if (UO->getOpcodeStr(UO->getOpcode()).compare("&")==0) {
				errs() << UO->getLocStart().printToString(Context->getSourceManager()) << " : Error" << " : Address of operator(&) prohibited.\n";
				compileCheckErrored = true;
			}
		}
		return true;
	}
	bool checkArray(QualType Q) {
		if (Q->isArrayType()) {
			return true;
		}
		else if (Q->isPointerType()) {
			return checkArray(Q->getPointeeType());
		}
		else {
			return false;
		}
	}
	bool VisitVarDecl(VarDecl *VD) {
		if (checkArray(VD->getType())) {
			errs() << VD->getLocStart().printToString(Context->getSourceManager()) << " : Error" << " : Array type declarations prohibited in variable declarations.\n";
			compileCheckErrored = true;
		}
		return true;
	}
	bool VisitFieldDecl(FieldDecl *FD) {
		if (checkArray(FD->getType())) {
			errs() << FD->getLocStart().printToString(Context->getSourceManager()) << " : Error" << " : Array type declarations prohibited in field declarations.\n";
			compileCheckErrored = true;
		}
		return true;
	}
	
};

class CollectStructInfoVisitor : public RecursiveASTVisitor<CollectStructInfoVisitor> {
private:
	ASTContext *Context;
	int UID;
public:
	
	bool VisitRecordDecl(RecordDecl *R) {
		if (R->getDefinition() != R)
			return true;
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
	explicit CollectStructInfoVisitor(ASTContext *Context) : Context(Context), UID(2) {
		UID_map["int"] = 0;
		UID_inv_map[0] = "int";
		UID_size_map[0] = 4;
		UID_map["char"] = 1;
		UID_inv_map[1] = "char";
		UID_size_map[1] = 1;

	}
};
class CreateStructDefsVisitor : public RecursiveASTVisitor<CreateStructDefsVisitor> {
private:
	ASTContext *Context;
public:
	bool VisitRecordDecl(RecordDecl *R) {
		if (R->getDefinition() != R)
			return true;
		int UID = UID_map[R->getName().str()];
		os << "// UID(" << R->getName().str() << ") = "<<UID<<std::endl;
		for (RecordDecl::field_iterator f = R->field_begin(); f != R->field_end(); f++) {
			os << "var $M." << R->getName().str() << "." << f->getName().str() << " : [int] int;" << std::endl;
		}
		// struct malloc
		os << "procedure malloc_" << R->getName().str() << "(n:int) returns (p:int) {" << std::endl;
		os << "\tcall p := $malloc(n*" << UID_size_map[UID] << ");" << std::endl;
		os << "\t$M._type[p] := " << UID << ";" << std::endl;
		os << "\t$M._size[p] := n;" << std::endl;

		os << "}" << std::endl;

		//struct cast 
		os << "procedure $cast_" << R->getName().str() << "(p:int) returns (q:int) {" << std::endl;
		os << "\tassert p == 0 || $M._alloc[p] == 1;" << std::endl;
		os << "\tassert p == 0 || $M._C[" << UID << "][$M._type[p]] == 1;" << std::endl;
		os << "\tassert p == 0 || $M._size[p] == 1;" << std::endl;
		os << "\tq := p;" << std::endl;
		os << "}" << std::endl;
		return true;
	}
	explicit CreateStructDefsVisitor(ASTContext *Context) : Context(Context) {}
};

class CreateFunctionDefinitionsVisitor : public RecursiveASTVisitor<CreateFunctionDefinitionsVisitor> {
private:
	ASTContext *Context;
	static int tempCount;
	static std::stringstream fs;
	static std::map<int, std::map<std::string, std::string>> symbolTable;
	static int symbolTableLevel;
	static std::unordered_set<std::string> varList;
	static int string_addr;
	static std::stringstream string_init;

	static int createStringConst(std::string s) {
		int t = string_addr;
		string_init << "\t" << "$M._type[" << string_addr << "] := 1;" << std::endl;
		for (const char *c = s.c_str(); *c != '\0'; c++) {
			string_init << "\t" << "$M.char[" << string_addr << "] := " << (int)*c << ";" << std::endl;
			string_addr++;
		}
		string_init << "\t" << "$M.char[" << string_addr << "] := 0;" << std::endl;
		string_addr++;
		return t;
	}

	static void symbolTableEnterLevel(void) {
		symbolTableLevel++;
		std::map<std::string, std::string> table;
		symbolTable[symbolTableLevel] = table;
	}
	static void symbolTableExitLevel(void) {
		symbolTable.erase(symbolTableLevel);
		symbolTableLevel--;
	}
	static void symbolTableCreateVar(std::string var) {
		std::stringstream ss;
		ss << var << "$" << symbolTableLevel;
		symbolTable[symbolTableLevel][var] = ss.str();
	}
	static std::string symbolTableGetVar(std::string var) {
		for (int i = symbolTableLevel; i >= 0; i--) {
			if (symbolTable[i].find(var) != symbolTable[i].end())
				return symbolTable[i][var];
		}
		return var;
	}
	static int getNextTemp() {
		int t = tempCount;
		tempCount++;
		return t;
	}
	static void resetTemp() {
		tempCount = 0;
	}
	static std::string getAsTemp(int n) {
		std::stringstream s;
		s << "$temp_" << n;
		return s.str();
	}
	static void generateTabs(int n) {
		fs << nTabs(n);
	}
	static std::string nTabs(int n) {
		std::stringstream s;
		for (int i = 0; i < n; i++)
			s << "\t";
		return s.str();
	}
	static std::string getTemporaryDeclarations() {
		std::stringstream s;
		for (int i = 0; i < tempCount; i++) {
			s << nTabs(1) << "var " << getAsTemp(i) << " : int;" << std::endl;
		}
		return s.str();
	}
	static int generateStructCopy(QualType t, int lhs_base, int rhs_base, int base_offset, int indent ) {
		RecordDecl *RD = t->getAsStructureType()->getDecl();
		for (RecordDecl::field_iterator f = RD->field_begin(); f != RD->field_end(); f++) {
			const QualType t = getBaseType((*f)->getType());
			std::string l_type = RD->getName().str();
			int offset = field_map[UID_map[l_type]][(*f)->getName().str()];
			if (t->isStructureType()) {
				generateStructCopy((*f)->getType(), lhs_base, rhs_base, offset, indent);
			}
			else {
				fs << nTabs(indent) << "$M." << l_type << "." << (*f)->getName().str() << "[" << getAsTemp(lhs_base) << " + " << offset + base_offset << "] := $M." << l_type << "." << (*f)->getName().str() << "[" << getAsTemp(rhs_base) << " + " << offset + base_offset << "];" << std::endl;
			}
		}
		return rhs_base;
	}
	static int getElementPtr(Expr *E, int indent) {
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
				fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(b) << "] != 0;" << std::endl;
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
				int t = generateStatement(UO->getSubExpr(), indent);
				fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
				return t;
			}
			else {
				fs << nTabs(indent) << "// Invalid operator found in getelementptr" << std::endl;
				return -1;
			}
		}
		else if (DeclRefExpr *DE = dyn_cast<DeclRefExpr>(E)) {
			int t = generateStatement(DE, indent);
			fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
			return t;
		}
		else if (ParenExpr *PE = dyn_cast<ParenExpr>(E)) {
			return getElementPtr(PE->getSubExpr(),indent);
		}
		else if (ArraySubscriptExpr *AE = dyn_cast<ArraySubscriptExpr>(E)) {
			int t = generateStatement(AE->getBase(), indent);
			int r = generateStatement(AE->getIdx(), indent);
			QualType type = AE->getBase()->getType()->getPointeeType();
			std::string type_name;
			if (type->isCharType()) {
				type_name = "char";
			}
			else if (type->isStructureType()) {
				type_name = type->getAsStructureType()->getDecl()->getName().str();
			}
			else {
				type_name = "int";
			}
			int size = UID_size_map[UID_map[type_name]];
			int address = getNextTemp();
			fs << nTabs(indent) << getAsTemp(address) << " := " << getAsTemp(t) << " + " << getAsTemp(r) << " * " << size << ";" << std::endl;
			fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
			fs << nTabs(indent) << "assert $M._size[" << getAsTemp(t) << "]" << " > " << getAsTemp(r) << ";" << std::endl;
			fs << nTabs(indent) << "assert " << getAsTemp(r) << " > " << "-1;" << std::endl;
			return address;
		}
		else {
		//	E->dump();
			fs << nTabs(indent) << "// Invalid expression found in getelementptr" << std::endl;
			return -1;
		}
		return -1;
	}
	static std::string getLValue(Expr *E, int indent) {
		if (DeclRefExpr *DE = dyn_cast<DeclRefExpr>(E)) {
			return symbolTableGetVar(DE->getDecl()->getName().str());
		}
		else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
			if (UO->getOpcodeStr(UO->getOpcode()).str().compare("*") == 0) {
				int t = generateStatement(UO->getSubExpr(), indent);
				std::stringstream ss;
				fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
				if (UO->getType()->isCharType())
					ss << "$M.char[" << getAsTemp(t) << "]";
				else
					ss << "$M.int[" << getAsTemp(t) << "]";
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
				fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(b) << "] != 0;" << std::endl;
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
		else if (ParenExpr *PE = dyn_cast<ParenExpr>(E)) {
			return getLValue(PE->getSubExpr(),indent);
		}
		else if (ArraySubscriptExpr *AE = dyn_cast<ArraySubscriptExpr>(E)) {
			int t = generateStatement(AE->getBase(), indent);
			int r = generateStatement(AE->getIdx(), indent);
			QualType type = AE->getBase()->getType()->getPointeeType();
			std::string type_name;
			if (type->isCharType()) {
				type_name = "char";
			}
			else {
				type_name = "int";
			}
			int size = UID_size_map[UID_map[type_name]];
			int address = getNextTemp();
			fs << nTabs(indent) << getAsTemp(address) << " := " << getAsTemp(t) << " + " << getAsTemp(r) << " * " << size << ";" << std::endl;
			fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
			fs << nTabs(indent) << "assert $M._size[" << getAsTemp(t) << "]" << " > " << getAsTemp(r) << ";" << std::endl;
			fs << nTabs(indent) << "assert " << getAsTemp(r) << " > " << "-1;" << std::endl;
			std::stringstream ss;
			ss << "$M." << type_name << "[" << getAsTemp(address) << "]" << std::endl;
			return ss.str();
		}
		else {
			fs << nTabs(indent) << "//Invalid lvalue found" << std::endl;
			return getAsTemp(-1);
		}
	}
	static int generateStatement(Stmt *S, int indent) {
		if (S == NULL)
			return -1;
		if (CompoundStmt *CS = dyn_cast<CompoundStmt>(S)) {
			int t = -1;
			symbolTableEnterLevel();
			for (CompoundStmt::body_iterator b = CS->body_begin(); b != CS->body_end(); b++) {
				t = generateStatement(*b, indent);
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
			else if (StringLiteral *SL = dyn_cast<StringLiteral>(E)) {
				int t = getNextTemp();
				fs << nTabs(indent) << getAsTemp(t) << " := " << createStringConst(SL->getString().str()) << ";" << std::endl;
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
				if (BO->getOpcodeStr().str().compare("+") == 0 || BO->getOpcodeStr().str().compare("-") == 0 || BO->getOpcodeStr().str().compare("*") == 0 || BO->getOpcodeStr().str().compare("/") == 0) {
					fs << nTabs(indent) << getAsTemp(t) << " := " << getAsTemp(lhs) << " " << BO->getOpcodeStr().str() << " " << getAsTemp(rhs) << ";" << std::endl;
				}
				else if (BO->getOpcodeStr().str().compare(">") == 0 || BO->getOpcodeStr().str().compare("<") == 0 || BO->getOpcodeStr().str().compare(">=") == 0 || BO->getOpcodeStr().str().compare("<=") == 0 || BO->getOpcodeStr().str().compare("==") == 0 || BO->getOpcodeStr().str().compare("!=") == 0) {
					fs << nTabs(indent) << "call " << getAsTemp(t) << " := $bool_to_int( " << getAsTemp(lhs) << " " << BO->getOpcodeStr().str() << " " << getAsTemp(rhs) << " );" << std::endl;
				}
				else if (BO->getOpcodeStr().str().compare("&&") == 0 || BO->getOpcodeStr().str().compare("||") == 0) {
					fs << nTabs(indent) << "call " << getAsTemp(t) << " := $bool_to_int( " << getAsTemp(lhs) << " != 0 " << BO->getOpcodeStr().str() << " " << getAsTemp(rhs) << " != 0);" << std::endl;
				}
				else {
					fs << nTabs(indent) << "// Binary operator not handled" << std::endl;
				}
				return t;
			}
			else if (CastExpr *CE = dyn_cast<CastExpr>(E)) {
				if (CE->getCastKind() == CK_LValueToRValue)
					return generateStatement(CE->getSubExpr(), indent);
				if (CE->getCastKind() != CK_BitCast && CE->getCastKind() != CK_NoOp) {
					fs << nTabs(indent) << "// Unknown cast type" << std::endl;
					return -1;
				}
				if (!(CE->getType()->isPointerType()))
					return generateStatement(CE->getSubExpr(), indent);

				if (CallExpr *CA = dyn_cast<CallExpr>(CE->getSubExpr())) {
					if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(CA->getCallee())) {
						if (DeclRefExpr *DE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())) {
							if (FunctionDecl *fdecl = dyn_cast<FunctionDecl>(DE->getFoundDecl())) {
								if (fdecl->getName().str().compare("typed_malloc")==0) {
									QualType ty = CE->getType()->getPointeeType();
									std::string tname;
									if (ty->isStructureType()) {
										tname = ty->getAsStructureType()->getDecl()->getName().str();
									}
									else if (ty->isCharType()) {
										tname = "char";
									}
									else {
										tname = "int";
									}
									int p = generateStatement(CA->getArgs()[0],indent);
									int r = getNextTemp();
									fs << nTabs(indent) << "call " << getAsTemp(r) << " := malloc_" << tname << "(" << getAsTemp(p) << ");" << std::endl;
									return r;
								}
							}
						}
					}
				}

				int t = generateStatement(CE->getSubExpr(), indent);
				QualType ty = CE->getType();
				int t_backup = t;
				while (ty->isPointerType()) {
					int r = getNextTemp();
					QualType sub_type = ty->getPointeeType();
					std::string tname;
					if (sub_type->isStructureType()) {
						tname = ty->getAsStructureType()->getDecl()->getName().str();
					}
					else if (sub_type->isVoidType()) {
						tname = "void";
					}
					else if (sub_type->isCharType()) {
						tname = "char";
					}
					else {
						tname = "int";
					}
					fs << nTabs(indent) << "call " << getAsTemp(r) << " := $cast_" << tname << "(" << getAsTemp(t) << ");" << std::endl;
					ty = sub_type;
					t = r;
					if (ty->isPointerType())
						fs << nTabs(indent) << getAsTemp(t) << " := $M.int[" << getAsTemp(t) << "];" << std::endl;
					
				}
				return t_backup;
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
			else if (ArraySubscriptExpr *AE = dyn_cast<ArraySubscriptExpr>(E)) {
				int t = generateStatement(AE->getBase(),indent);
				int r = generateStatement(AE->getIdx(), indent);
				QualType type = AE->getBase()->getType()->getPointeeType();
				std::string type_name;
				if (type->isCharType()) {
					type_name = "char";
				}
				else {
					type_name = "int";
				}
				int size = UID_size_map[UID_map[type_name]];
				int address = getNextTemp();
				fs << nTabs(indent) << getAsTemp(address) << " := " << getAsTemp(t) << " + " << getAsTemp(r) << " * " << size << ";" << std::endl;
				fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
				fs << nTabs(indent) << "assert $M._size[" << getAsTemp(t) << "]" << " > " << getAsTemp(r) << ";" << std::endl;
				fs << nTabs(indent) << "assert " << getAsTemp(r) << " > " << "-1;" << std::endl;
				int value = getNextTemp();
				fs << nTabs(indent) << getAsTemp(value) << " := $M." << type_name << "[" << getAsTemp(address) << "];" << std::endl;
				return value;
			}
			else if (UnaryOperator *UO = dyn_cast<UnaryOperator>(E)) {
				//fs << nTabs(indent) << "// Unary operator " << UO->getOpcodeStr(UO->getOpcode()).str() << std::endl;
				if (UO->getOpcodeStr(UO->getOpcode()).str().compare("-") == 0) {
					int t = generateStatement(UO->getSubExpr(), indent);
					fs << nTabs(indent) << getAsTemp(t) << " := 0 - " << getAsTemp(t) << ";" << std::endl;
					return t;
				}
				else if (UO->getOpcodeStr(UO->getOpcode()).str().compare("!") == 0) {
					int t = generateStatement(UO->getSubExpr(), indent);
					fs << nTabs(indent) << "if ( " << getAsTemp(t) << " == 0 )" << std::endl;
					fs << nTabs(indent + 1) << getAsTemp(t) << " := 1;" << std::endl;
					fs << nTabs(indent) << "else" << std::endl;
					fs << nTabs(indent + 1) << getAsTemp(t) << " := 0;" << std::endl;
					return(t);
				}
				else if (UO->getOpcodeStr(UO->getOpcode()).str().compare("*") == 0) {
					int t = generateStatement(UO->getSubExpr(), indent);
					fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(t) << "] != 0;" << std::endl;
					if (UO->getType()->isCharType())
						fs << nTabs(indent) << getAsTemp(t) << " := $M.char[" << getAsTemp(t) << "];" << std::endl;
					else
						fs << nTabs(indent) << getAsTemp(t) << " := $M.int[" << getAsTemp(t) << "];" << std::endl;
					
					return(t);
				}
				else if (UO->isPrefix()) {
					std::string variable = getLValue(UO->getSubExpr(), indent);
					int t = getNextTemp();
					std::string op = UO->isIncrementOp() ? "+" : "-";
					fs << nTabs(indent) << variable << " := " << variable << " " << op << "1;" << std::endl;
					fs << nTabs(indent) << getAsTemp(t) << " := " << variable << ";" << std::endl;
					return t;
				}
				else if (UO->isPostfix()) {
					std::string variable = getLValue(UO->getSubExpr(), indent);
					int t = getNextTemp();
					std::string op = UO->isIncrementOp() ? "+" : "-";
					fs << nTabs(indent) << getAsTemp(t) << " := " << variable << ";" << std::endl;
					fs << nTabs(indent) << variable << " := " << variable << " " << op << "1;" << std::endl;
					return t;
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
				return t;
			}
			else if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
				Expr *base = ME->getBase();
				int b;

				int t = getNextTemp();
				std::string l_type;
				if (ME->isArrow()) {
					l_type = base->getType()->getPointeeType()->getAsStructureType()->getDecl()->getName().str();
					b = generateStatement(base, indent);
					fs << nTabs(indent) << "assert $M._alloc[" << getAsTemp(b) << "] != 0;" << std::endl;
				}
				else {
					b = getElementPtr(base, indent);
					l_type = base->getType()->getAsStructureType()->getDecl()->getName().str();
				}
				int offset = field_map[UID_map[l_type]][ME->getMemberDecl()->getName().str()];
				fs << nTabs(indent) << getAsTemp(t) << " := $M." << l_type << "." << ME->getMemberDecl()->getName().str() << "[" << getAsTemp(b) << " + " << offset << "];" << std::endl;
				return t;
			}
			else if (ParenExpr *PE = dyn_cast<ParenExpr>(E)) {
				return generateStatement(PE->getSubExpr(),indent);
			}
			else {
				generateTabs(indent);
				fs << "//Expr Not Handled yet!" << std::endl;
				return -1;
			}
		}
		else if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
			int t = -1;
			if (RS->getRetValue()) {
				t = generateStatement(RS->getRetValue(), indent);
				fs << nTabs(indent) << "$return := " << getAsTemp(t) << ";" << std::endl;
			}
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
		else if (IfStmt *IS = dyn_cast<IfStmt>(S)) {
			int cond = generateStatement(IS->getCond(), indent);
			fs << nTabs(indent) << "if ( " << getAsTemp(cond) << " != 0 ) {" << std::endl;
			generateStatement(IS->getThen(), indent + 1);
			if (IS->getElse() != NULL) {
				fs << nTabs(indent) << "} else {" << std::endl;
				generateStatement(IS->getElse(), indent + 1);
			}
			fs << nTabs(indent) << "}" << std::endl;
			return -1;
		}
		else if (WhileStmt *WS = dyn_cast<WhileStmt>(S)) {
			int t = getNextTemp();
			int p = generateStatement(WS->getCond(), indent);
			fs << nTabs(indent) << getAsTemp(t) << " := " << getAsTemp(p) << ";" << std::endl;
			fs << nTabs(indent) << "while ( " << getAsTemp(t) << " != 0 ) {" << std::endl;
			generateStatement(WS->getBody(), indent + 1);
			p = generateStatement(WS->getCond(), indent + 1);
			fs << nTabs(indent + 1) << getAsTemp(t) << " := " << getAsTemp(p) << ";" << std::endl;
			fs << nTabs(indent) << "}" << std::endl;
			return -1;
		}
		else if (ForStmt *FS = dyn_cast<ForStmt>(S)) {
			int t = getNextTemp();
			generateStatement(FS->getInit(), indent);
			int p = generateStatement(FS->getCond(), indent);
			fs << nTabs(indent) << getAsTemp(t) << " := " << getAsTemp(p) << ";" << std::endl;
			fs << nTabs(indent) << "while ( " << getAsTemp(t) << " != 0 ) {" << std::endl;
			generateStatement(FS->getBody(), indent + 1);
			generateStatement(FS->getInc(), indent + 1);
			p = generateStatement(FS->getCond(), indent + 1);
			fs << nTabs(indent + 1) << getAsTemp(t) << " := " << getAsTemp(p) << ";" << std::endl;
			fs << nTabs(indent) << "}" << std::endl;
			return -1;
		}
		else if (BreakStmt *BS = dyn_cast<BreakStmt>(E)) {
			fs << nTabs(indent) << "break;" << std::endl;
			return -1;
		}
		else {
			generateTabs(indent);
			fs << "//Stmt Not Handled yet!"<<std::endl;
			return -1;
		}
	}
public:
	bool VisitVarDecl(VarDecl *VD) {
		if (VD->hasGlobalStorage()) {
			symbolTableCreateVar(VD->getName().str());
			os << "var " << symbolTableGetVar(VD->getName().str()) << " : int;" << "\n";
			if (VD->hasInit()) {
				globalInits.insert(VD);
			}
		}
		return true;
	}
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
				varList.insert(symbolTableGetVar((*p)->getName().str()));
				fs << "\t" << symbolTableGetVar((*p)->getName().str()) << " := $malloc_" << (*p)->getType()->getAsStructureType()->getDecl()->getName().str() << "(1);" << std::endl;
				fs << "\t" << getAsTemp(rhs_base) << " := " << symbolTableGetVar((*p)->getName().str()) << ";" << std::endl;
				generateStructCopy((*p)->getType(), lhs_base, rhs_base, 0, 1);
			}
			else {
				os << (*p)->getName().str() << "$immut : int";
				symbolTableCreateVar((*p)->getName().str());
				varList.insert(symbolTableGetVar((*p)->getName().str()));
				fs << "\t" << symbolTableGetVar((*p)->getName().str()) << " := " << (*p)->getName().str() << "$immut;" << std::endl;
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
		os << "}" << std::endl;
		symbolTableExitLevel();
		return true;
	}
	static void generateInitializeFunction(void) {
		os << "procedure {:entrypoint} $initialize() {" << std::endl;
		fs.str(std::string());
		fs << "\t" << "$currAddr := "<<string_addr<<";" << std::endl;
		for (std::map<std::string, int>::iterator it = UID_map.begin(); it != UID_map.end(); it++) {
			fs << "\t" << "$M._typesize[" << it->second << "] := " << UID_size_map[it->second] << ";" << std::endl;
			for (std::map<std::string, int>::iterator it2 = UID_map.begin(); it2 != UID_map.end(); it2++) {
				fs << "\t" << "$M._C[" << it->second << "][" << it2->second << "] := " << ((it->second == it2->second) ? 1 : 0) << ";" << std::endl;
			}
		}
		fs << string_init.str();
		resetTemp();
		for (std::set<VarDecl*>::iterator it = globalInits.begin(); it != globalInits.end(); it++) {
			VarDecl *VD = *it;
			if (VD->getType()->isStructureType()) {
				int rhs_base = getElementPtr(VD->getInit(), 1);
				int lhs_base = getNextTemp();
				fs << "\t" << getAsTemp(lhs_base) << " := " << symbolTableGetVar(VD->getName().str()) << ";" << std::endl;
				generateStructCopy(VD->getType(), lhs_base, rhs_base, 0, 1);
			}
			else {
				int t = generateStatement(VD->getInit(), 1);
				fs << "\t" << symbolTableGetVar(VD->getName().str()) << " := " << getAsTemp(t) << ";" << std::endl;
			}
		}
		
		int t = getNextTemp();
		fs << "\t" << "call " << getAsTemp(t) << " := main();" << std::endl;
		os << getTemporaryDeclarations();
		os << fs.str();	
		os << "}" << std::endl;
	}
	explicit CreateFunctionDefinitionsVisitor(ASTContext *Context) : Context(Context) {}
};

int CreateFunctionDefinitionsVisitor::symbolTableLevel = 0;
int CreateFunctionDefinitionsVisitor::tempCount = 0;
std::stringstream CreateFunctionDefinitionsVisitor::fs;
std::map<int, std::map<std::string, std::string>> CreateFunctionDefinitionsVisitor::symbolTable;
std::unordered_set<std::string> CreateFunctionDefinitionsVisitor::varList;
std::stringstream CreateFunctionDefinitionsVisitor::string_init;
int CreateFunctionDefinitionsVisitor::string_addr = 1024;
class BoogieGenConsumer : public clang::ASTConsumer {
private:
	CompileChecksVisitor Visitor0;
	CollectStructInfoVisitor Visitor1;
	CreateStructDefsVisitor Visitor2;
	CreateFunctionDefinitionsVisitor Visitor3;
	
public:
	virtual void HandleTranslationUnit(clang::ASTContext &Context) {
		Visitor0.TraverseDecl(Context.getTranslationUnitDecl());
		if (compileCheckErrored)
			return;
		generateFixedCode();
		Visitor1.TraverseDecl(Context.getTranslationUnitDecl());
		Visitor2.TraverseDecl(Context.getTranslationUnitDecl());
		Visitor3.TraverseDecl(Context.getTranslationUnitDecl());
		CreateFunctionDefinitionsVisitor::generateInitializeFunction();
	}
	explicit BoogieGenConsumer(ASTContext *Context) :Visitor0(Context), Visitor1(Context), Visitor2(Context), Visitor3(Context) {}
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
		std::fstream f;
		f.open("test.bpl", std::ios::out);
		f << os.str();
		f.close();
		return 0;
	}
}
