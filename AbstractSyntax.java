// Abstract syntax for the language C++Lite,
// exactly as it appears in Appendix B.

import java.util.*;

class Program {
    // Program = Declarations decpart ; Block body
    Declarations globals;
    Functions functions;

    Program (Declarations d, Block b) {
        this.globals = globals;
        this.functions = functions;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Program : ");
        gloabls.display(level+ 1);
        functions.display(level + 1);
    }
}
class Functions extends ArrayList<Function> {
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Functions : ");
        for(Function function : this){
            function.display(level+1);
            system.out.println();
        }
    }
}
class Function {
    Type t;
    String id;
    Declarations params, locals;
    Block body;

    public Function(Type t, String id, Declarations params, Declarations locals, Block body) {
        this.t = t;
        this.id = id;
        this.params = params;
        this.locals = locals;
        this.body = body;
    }

    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Function = " + id + "; Return type = " + type.getId());
        level++;
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Parameters : ");
        params.display(level + 1);
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Locals : ");
        locals.display(level + 1);
        body.display(level);
    }
}
class Call extends Expression {
    String name;
    Expressions args;

    Call(String name, Expressions args) {
        this.name = name;
        this.args = args;
    }

    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Call: " + name);
        args.display(level + 1);
    }
}


class Declarations extends ArrayList<Declaration> {
    // Declarations = Declaration*
    // (a list of declarations d1, d2, ..., dn)
    public void display(int level) {
        System.out.print("\t");
//        System.out.println("Declaractions: ");
        for (int i = 0; i < level; i++)
            System.out.print("\t");
//        System.out.print("Declaractions: {");
        for (int i = 0; i < size(); i++)
            get(i).display(level);
//        System.out.println("}");
    }
}

class Declaration {
// Declaration = Variable v; Type t
    Variable v;
    Type t;

    Declaration (Variable var, Type type) {
        v = var; t = type;
    } // declaration */
    public void display(int level) {
      //  System.out.print(" <" + t + ", " + v + "> ");
    }
}

class Type {
    // Type = int | bool | char | float 
    final static Type INT = new Type("int");
    final static Type BOOL = new Type("bool");
    final static Type CHAR = new Type("char");
    final static Type FLOAT = new Type("float");
    final static Type VOID = new Type("void");
    final static Type UNDEFINED = new Type("undef");
    
    private String id;

    private Type (String t) { id = t; }

    public String toString ( ) { return id; }
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null || getClass() != obj.getClass())
            return false;
        Type other = (Type) obj;
        return id.equals(other.id);
    }

    public int hashCode() {
        return Objects.hash(id);
    }
}

abstract class Statement {
    // Statement = Skip | Block | Assignment | Conditional | Loop
    public void display(int level) {
    }
}


class Skip extends Statement {
}

class Block extends Statement {
    // Block = Statement*
    //         (a Vector of members)
    public ArrayList<Statement> members = new ArrayList<Statement>();
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
//        System.out.println("Blocks: ");
        System.out.println();
        for (Statement st : members)
            st.display(level);
    }
}
class Prototype extends Type {
    Declarations params; // 반환형은 Type에 의해 상속받음
    Prototype(Type returnType, Declarations params) {
        super(returnType.toString());
        this.params = params;
    }

    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Prototype: Return type = " + this.toString());

        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Parameters : ");
        params.display(level + 1);
    }

}
class Assignment extends Statement {
    // Assignment = Variable target; Expression source
    Variable target;
    Expression source;

    Assignment (Variable t, Expression e) {
        target = t;
        source = e;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print(" \t");
//        System.out.println("Assignment: ");
        System.out.println("=");
        target.display(level + 1);
        source.display(level + 1);
    }
}

class Conditional extends Statement {
// Conditional = Expression test; Statement thenbranch, elsebranch
    Expression test;
    Statement thenbranch, elsebranch;
    // elsebranch == null means "if... then"

    Conditional (Expression t, Statement tp) {
        test = t; thenbranch = tp; elsebranch = new Skip( );
    }
    
    Conditional (Expression t, Statement tp, Statement ep) {
        test = t; thenbranch = tp; elsebranch = ep;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("IfStatement:");

        test.display(level + 1);
        thenbranch.display(level + 1);
        elsebranch.display(level + 1);
    }
}

class Loop extends Statement {
// Loop = Expression test; Statement body
    Expression test;
    Statement body;

    Loop (Expression t, Statement b) {
        test = t; body = b;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("WhileStatement:");
        test.display(level + 1);
        body.display(level + 1);
    }
}
class Return extends Statement {
    Variable target;
    Expression result;

    public Return(Variable target, Expression result) {
        this.target = target;
        this.result = result;
    }

    public void display(int level) {
        super.display(level);
        target.display(level + 1);
        retVal.display(level + 1);
    }
}
class Expressions extends ArrayList<Expression> {
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("Expressions:");
        for (Expression expression : this) {
            expression.display(level + 1);
        }
    }
}
class Expression extends Statement {
    private Value value;

    public Expression(Value value) {
        this.value = value;
    }

    @Override
    public void display(int level) {
        System.out.println("Expression :");
        value.display(level);
    }
}
abstract class Expression {
    // Expression = Variable | Value | Binary | Unary
    public void display(int level) {
    }
}

class Variable extends Expression {
    // Variable = String id
    private String id;

    Variable (String s) { id = s; }

    public String toString( ) { return id; }
    
    public boolean equals (Object obj) {
        String s = ((Variable) obj).id;
        return id.equals(s); // case-sensitive identifiers
    }
    
    public int hashCode ( ) { return id.hashCode( ); }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println(id);
    }
}

abstract class Value extends Expression {
    // Value = IntValue | BoolValue |
    //         CharValue | FloatValue
    protected Type type;
    protected boolean undef = true;

    int intValue ( ) {
        assert false : "should never reach here";
        return 0;
    }
    
    boolean boolValue ( ) {
        assert false : "should never reach here";
        return false;
    }
    
    char charValue ( ) {
        assert false : "should never reach here";
        return ' ';
    }
    
    float floatValue ( ) {
        assert false : "should never reach here";
        return 0.0f;
    }

    boolean isUndef( ) { return undef; }
    boolean isUndefined() {
        return undef;
    }

    boolean isUnused() {
        return false;
    }
    Type type ( ) { return type; }

    static Value mkValue (Type type) {
        if (type == Type.INT) return new IntValue( );
        if (type == Type.BOOL) return new BoolValue( );
        if (type == Type.CHAR) return new CharValue( );
        if (type == Type.FLOAT) return new FloatValue( );
        if(type==Type.UNDEFINED) return new UndefinedValue();
        if(type==Type.UNUNSED) return new UnusedValue();

        throw new IllegalArgumentException("Illegal type in mkValue");
    }
}

class IntValue extends Value {
    private int value = 0;

    IntValue() {
        type = Type.INT;
    }

    IntValue(int v) {
        this();
        value = v;
        undef = false;
    }

    int intValue() {
        assert !undef : "reference to undefined int value";
        return value;
    }

    public String toString() {
        if (undef) return "undef";
        return "" + value;
    }

    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println( value);

    }
}
class BoolValue extends Value {
    private boolean value = false;

    BoolValue ( ) { type = Type.BOOL; }

    BoolValue (boolean v) { this( ); value = v; undef = false; }

    boolean boolValue ( ) {
        assert !undef : "reference to undefined bool value";
        return value;
    }

    int intValue ( ) {
        assert !undef : "reference to undefined bool value";
        return value ? 1 : 0;
    }

    public String toString( ) {
        if (undef)  return "undef";
        return "" + value;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println(value);
    }
}

class CharValue extends Value {
    private char value = ' ';

    CharValue ( ) { type = Type.CHAR; }

    CharValue (char v) { this( ); value = v; undef = false; }

    char charValue ( ) {
        assert !undef : "reference to undefined char value";
        return value;
    }

    public String toString( ) {
        if (undef)  return "undef";
        return "" + value;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println(value);
    }
}

class FloatValue extends Value {
    private float value = 0;

    FloatValue ( ) { type = Type.FLOAT; }

    FloatValue (float v) { this( ); value = v; undef = false; }

    float floatValue ( ) {
        assert !undef : "reference to undefined float value";
        return value;
    }

    public String toString( ) {
        if (undef)  return "undef";
        return "" + value;
    }
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println(value);
    }
}
class UndefinedValue extends Value {
    UndefinedValue() {type=Type.UNDEFINED; undef=true;}
    // display()
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("UndefinedValue: " + type);
    }
}
class UnusedValue extends Value {
    UnusedValue() {type=Type.UNUSED; undef=true;}
    // display()
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
        System.out.println("UnusedValue: " + type);
    }
}
class Binary extends Expression {
// Binary = Operator op; Expression term1, term2
    Operator op;
    Expression term1, term2;

    Binary (Operator o, Expression l, Expression r) {
        op = o; term1 = l; term2 = r;
    } // binary
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
//        System.out.print("Binary: ");
        op.display(level + 1);
        term1.display(level + 1);
        term2.display(level + 1);
    }

    public String toString() {
        return ("Binary: op=" + op + "term1=" + term1 + "term2=" + term2);
    }
}

class Unary extends Expression {
    // Unary = Operator op; Expression term
    Operator op;
    Expression term;

    Unary (Operator o, Expression e) {
        op = o; term = e;
    } // unary
    public void display(int level) {
        for (int i = 0; i < level; i++)
            System.out.print("\t");
//        System.out.println("Unary: ");
        op.display(level + 1);
        term.display(level + 1);
    }
}

class Operator {
    // Operator = BooleanOp | RelationalOp | ArithmeticOp | UnaryOp
    // BooleanOp = && | ||
    final static String AND = "&&";
    final static String OR = "||";
    // RelationalOp = < | <= | == | != | >= | >
    final static String LT = "<";
    final static String LE = "<=";
    final static String EQ = "==";
    final static String NE = "!=";
    final static String GT = ">";
    final static String GE = ">=";
    // ArithmeticOp = + | - | * | /
    final static String PLUS = "+";
    final static String MINUS = "-";
    final static String TIMES = "*";
    final static String DIV = "/";
    // UnaryOp = !
    final static String NOT = "!";
    final static String NEG = "neg";
    // CastOp = int | float | char
    final static String INT = "int";
    final static String FLOAT = "float";
    final static String CHAR = "char";
    // Typed Operators
    // RelationalOp = < | <= | == | != | >= | >
    final static String INT_LT = "INT<";
    final static String INT_LE = "INT<=";
    final static String INT_EQ = "INT==";
    final static String INT_NE = "INT!=";
    final static String INT_GT = "INT>";
    final static String INT_GE = "INT>=";
    // ArithmeticOp = + | - | * | /
    final static String INT_PLUS = "INT+";
    final static String INT_MINUS = "INT-";
    final static String INT_TIMES = "INT*";
    final static String INT_DIV = "INT/";
    // UnaryOp = !
    final static String INT_NEG = "INTNEG";
    // RelationalOp = < | <= | == | != | >= | >
    final static String FLOAT_LT = "FLOAT<";
    final static String FLOAT_LE = "FLOAT<=";
    final static String FLOAT_EQ = "FLOAT==";
    final static String FLOAT_NE = "FLOAT!=";
    final static String FLOAT_GT = "FLOAT>";
    final static String FLOAT_GE = "FLOAT>=";
    // ArithmeticOp = + | - | * | /
    final static String FLOAT_PLUS = "FLOAT+";
    final static String FLOAT_MINUS = "FLOAT-";
    final static String FLOAT_TIMES = "FLOAT*";
    final static String FLOAT_DIV = "FLOAT/";
    // UnaryOp = !
    final static String FLOAT_NEG = "FLOATNEG";
    // RelationalOp = < | <= | == | != | >= | >
    final static String CHAR_LT = "CHAR<";
    final static String CHAR_LE = "CHAR<=";
    final static String CHAR_EQ = "CHAR==";
    final static String CHAR_NE = "CHAR!=";
    final static String CHAR_GT = "CHAR>";
    final static String CHAR_GE = "CHAR>=";
    // RelationalOp = < | <= | == | != | >= | >
    final static String BOOL_LT = "BOOL<";
    final static String BOOL_LE = "BOOL<=";
    final static String BOOL_EQ = "BOOL==";
    final static String BOOL_NE = "BOOL!=";
    final static String BOOL_GT = "BOOL>";
    final static String BOOL_GE = "BOOL>=";
    // Type specific cast
    final static String I2F = "I2F";
    final static String F2I = "F2I";
    final static String C2I = "C2I";
    final static String I2C = "I2C";

    String val;

    Operator (String s) { val = s; }

    public String toString( ) { return val; }
    public boolean equals(Object obj) { return val.equals(obj); }

    boolean BooleanOp ( ) { return val.equals(AND) || val.equals(OR); }
    boolean RelationalOp ( ) {
        return val.equals(LT) || val.equals(LE) || val.equals(EQ)
            || val.equals(NE) || val.equals(GT) || val.equals(GE);
    }
    boolean ArithmeticOp ( ) {
        return val.equals(PLUS) || val.equals(MINUS)
            || val.equals(TIMES) || val.equals(DIV);
    }
    boolean NotOp ( ) { return val.equals(NOT) ; }
    boolean NegateOp ( ) { return val.equals(NEG) ; }
    boolean intOp ( ) { return val.equals(INT); }
    boolean floatOp ( ) { return val.equals(FLOAT); }
    boolean charOp ( ) { return val.equals(CHAR); }

    final static String intMap[ ] [ ] = {
        {PLUS, INT_PLUS}, {MINUS, INT_MINUS},
        {TIMES, INT_TIMES}, {DIV, INT_DIV},
        {EQ, INT_EQ}, {NE, INT_NE}, {LT, INT_LT},
        {LE, INT_LE}, {GT, INT_GT}, {GE, INT_GE},
        {NEG, INT_NEG}, {FLOAT, I2F}, {CHAR, I2C}
    };

    final static String floatMap[ ] [ ] = {
        {PLUS, FLOAT_PLUS}, {MINUS, FLOAT_MINUS},
        {TIMES, FLOAT_TIMES}, {DIV, FLOAT_DIV},
        {EQ, FLOAT_EQ}, {NE, FLOAT_NE}, {LT, FLOAT_LT},
        {LE, FLOAT_LE}, {GT, FLOAT_GT}, {GE, FLOAT_GE},
        {NEG, FLOAT_NEG}, {INT, F2I}
    };

    final static String charMap[ ] [ ] = {
        {EQ, CHAR_EQ}, {NE, CHAR_NE}, {LT, CHAR_LT},
        {LE, CHAR_LE}, {GT, CHAR_GT}, {GE, CHAR_GE},
        {INT, C2I}
    };

    final static String boolMap[ ] [ ] = {
        {EQ, BOOL_EQ}, {NE, BOOL_NE}, {LT, BOOL_LT},
        {LE, BOOL_LE}, {GT, BOOL_GT}, {GE, BOOL_GE},
    };

    final static private Operator map (String[][] tmap, String op) {
        for (int i = 0; i < tmap.length; i++)
            if (tmap[i][0].equals(op))
                return new Operator(tmap[i][1]);
        assert false : "should never reach here";
        return null;
    }

    final static public Operator intMap (String op) {
        return map (intMap, op);
    }

    final static public Operator floatMap (String op) {
        return map (floatMap, op);
    }

    final static public Operator charMap (String op) {
        return map (charMap, op);
    }

    final static public Operator boolMap (String op) {
        return map (boolMap, op);
    }
    public void display(int level) {
        System.out.println(val);
    }
}

