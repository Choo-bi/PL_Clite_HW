import java.util.*;

public class Parser {
    // Recursive descent parser that inputs a C++Lite program and 
    // generates its abstract syntax.  Each method corresponds to
    // a concrete syntax grammar rule, which appears as a comment
    // at the beginning of the method.
  
    Token token;          // current token from the input stream
    Lexer lexer;

    public Parser(Lexer ts) { // Open the C++Lite source program
        lexer = ts;                          // as a token stream, and
        token = lexer.next();            // retrieve its first Token
    }
  
    private String match (TokenType t) {
        String value = token.value();
        System.out.println(token.type() + " " + token.value());
        if (token.type().equals(t))
            token = lexer.next();
        else
            error(t);
        return value;
    }

    private void error(TokenType tok) {
        System.err.println("Syntax error: expecting: " + tok 
                           + "; saw: " + token);
        System.exit(1);
    }
  
    private void error(String tok) {
        System.err.println("Syntax error: expecting: " + tok 
                           + "; saw: " + token);
        System.exit(1);
    }

    public Program program() {
// Program --> { Type Identifier FunctionOrGlobal } MainFunction
        Program prog = new Program();
        prog.globals = new Declarations();
        prog.functions = new Functions();
        Type t;
        Declaration d;
        Function f;
        while (!token.type().equals(TokenType.Eof)) {
            t = type();
            if (token.type().equals(TokenType.Identifier)) {
                d = new Declaration(token.value(), t);
                token = lexer.next();
                TokenType tt = token.type();
                if (tt.equals(TokenType.Comma) || tt.equals(TokenType.Semicolon)) {
                    prog.globals.add(d);
                    while (token.type().equals(TokenType.Comma)) {
                        token = lexer.next();
                        d = new Declaration(token.value(), t);
                        prog.globals.add(d);
                        token = lexer.next();
                    }
                    token = lexer.next();
                } // globals
                else if (tt.equals(TokenType.LeftParen)) {
                    f = new Function(d.v.id(), t);
                    funcId = d.v.id();
                    token = lexer.next(); // skip left parenthesis
                    f = functionRest(f);
                    prog.functions.add(f);
                } else error("FunctionOrGlobal");
            } else error("Identifier");
            return prog;
        }
    }
    private Function functionRest(Function f) {
        // functionRest --> Parameters ) { Declarations Statements }
        // Parameters --> [ Parameter { , Parameter } ]
        f.params = new Declarations();
        while(token.type().equals(TokenType.Int) ||
                token.type().equals(TokenType.Float) ||
                token.type().equals(TokenType.Char) ||
                token.type().equals(TokenType.Bool)) {
            f.params=parameter(f.params);
            if(token.type().equals(TokenType.Comma))
                match(TokenType.Comma);
        }
        match(TokenType.RightParen);
        match(TokenType.LeftBrace);
        f.locals = declarations();
        f.body = statements();
        match(TokenType.RightBrace);
        return f;
    }
    private Declarations parameter(Declarations params) {
        // Parameter --> Type Identifier
        Declaration d = new Declaration();
        d.t = new Type(token.value());
        token = lexer.next();
        if(token.type().equals(TokenType.Identifier)) {
            d.v = new Variable(match(TokenType.Identifier));
        } else error("identifier");
        params.add(d);
        return params;
    }
    private Declarations declarations () {
        // Declarations --> { Declaration }
        Declarations dec = new Declarations();
        while (isType()) {
            declaration(dec);
        }
        return dec;
    }
  
    private void declaration (Declarations ds) {
        // Declaration  --> Type Identifier { , Identifier } ;
        Type t = type();
        Variable v = new Variable(match(TokenType.Identifier));
        Declaration d = new Declaration(v, t);
        ds.add(d);
        while(token.type().equals(TokenType.Comma)){
            match(TokenType.Comma);
            v = new Variable(match(TokenType.Identifier));
            d = new Declaration(v,t);
            ds.add(d);
        }
        match(TokenType.Semicolon);
    }
  
    private Type type () {
        // Type  -->  int | bool | float | char 
        Type t = null;
        if (token.type() == TokenType.Int)
            t = Type.INT;
        else if (token.type() == TokenType.Bool)
            t = Type.BOOL;
        else if (token.type() == TokenType.Float)
            t = Type.FLOAT;
        else if (token.type() == TokenType.Char)
            t = Type.CHAR;
        else if (token.type().equals(TokenType.Void))
            t=Type.VOID;
        else
            error("int | bool | float | char | void");
        token = lexer.next();
        return t;          
    }

    private Statement statement() {
        // Statement --> ; | Block | Assignment | IfStatement | WhileStatement | Call
        Statement s= null;
        if(token.type().equals(TokenType.Semicolon))
            s = new Skip(); //semicolon
        else if(token.type().equals(TokenType.LeftBrace)){
            match(TokenType.LeftBrace);
            s = statements();
            match(TokenType.RightBrace);
        }
        else if(token.type().equals(TokenType.Identifier)){
            s = assignment();
        }
        else if(token.type().equals(TokenType.If)){
            s= ifStatement();
        }
        else if(token.type().equals(TokenType.While)){
            s= whileStatement();
        }
        else if(token.type().equals(TokenType.Identifier))
            s=assignOrCall();
        else if(token.type().equals(TokenType.Return))
            s=returnStatement();

        else{
            error(token.type());
        }
        // student exercise
        return s;
    }
    private Statement returnStatement() {
        Return r = new Return();
        match(TokenType.Return); // skip return keyword
        r.target = new Variable(funcId);
        r.result = expression();
        match(TokenType.Semicolon);
        return r;
    }
    private Statement assignOrCall() {
        Variable v=new Variable(token.value());
        Call c=new Call();
        token=lexer.next(); // skip identifier
        if(token.type().equals(TokenType.Assign)) {
            token=lexer.next();
            Expression src=expression();
            match(TokenType.Semicolon);
            return new Assignment(v, src);
        } else if(token.type().equals(TokenType.LeftParen)) {
            c.name=v.id();
            token=lexer.next(); // skip left parenthesis
            c.args = arguments();
            match(TokenType.RightParen);
            match(TokenType.Semicolon);
            return c;
        }  else error("assignOrCall");
        return null; // should not reach here!
    }
    private Expressions arguments() {
        // Arguments --> [ Expression { , Expression } ]
        Expressions args = new Expressions();
        while(!token.type().equals(TokenType.RightParen)) {
            args.add(expression());
            if(token.type().equals(TokenType.Comma))
                match(TokenType.Comma);
            else if(!token.type().equals(TokenType.RightParen))
                error("Expression");
        }
        if(args.size() == 0)
            args = null;
        return args;
    }


    private Block statements () {
        // Block --> '{' Statements '}'
        Block b = new Block();
        while(!token.type().equals(TokenType.RightBrace)) {
            Statement s = statement();
            b.members.add(s);
        }
        return b;
    }
  
    private Assignment assignment () {
        // Assignment --> Identifier = Expression ;
        Variable target = new Variable(match(TokenType.Identifier));
        match(TokenType.Assign);
        Expression source = expression();
        match(TokenType.Semicolon);
        return new Assignment(target, source);
    }
  
    private Conditional ifStatement () {
        // IfStatement --> if ( Expression ) Statement [ else Statement ]
        match(TokenType.If);
        match(TokenType.LeftParen);
        Expression ex = expression();
        match(TokenType.RightParen);
        Statement consequent = statement();
        if (token.type().equals(TokenType.Else)) {
            match(TokenType.Else);
            Statement alternative = statement();
            return new Conditional(ex, consequent, alternative);
        } else {
            return new Conditional(ex, consequent);
        }
    }

    private Loop whileStatement () {
        // WhileStatement --> while ( Expression ) Statement
        match(TokenType.While);
        match(TokenType.LeftParen);
        Expression ex = expression();
        match(TokenType.RightParen);
        Statement body = statement();
        return new Loop(ex, body);
    }

    private Expression expression () {
        // Expression --> Conjunction { || Conjunction }
        Expression e = conjunction();
        while (token.type().equals(TokenType.Or)) {
            Operator op = new Operator(match(TokenType.Or));
            Expression term2 = conjunction();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression conjunction () {
        // Conjunction --> Equality { && Equality }
        Expression e = equality();
        while (token.type().equals(TokenType.And)) {
            Operator op = new Operator(match(TokenType.And));
            Expression term2 = equality();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression equality () {
        // Equality --> Relation [ EquOp Relation ]
        Expression e = relation();
        while (isEqualityOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = relation();
            e = new Binary(op, e, term2);
        }
        return e;
    }

    private Expression relation (){
        // Relation --> Addition [RelOp Addition] 
        Expression e = addition();
        while (isRelationalOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = addition();
            e = new Binary(op, e, term2);
        }
        return e;// student exercise
    }
  
    private Expression addition () {
        // Addition --> Term { AddOp Term }
        Expression e = term();
        while (isAddOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = term();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression term () {
        // Term --> Factor { MultiplyOp Factor }
        Expression e = factor();
        while (isMultiplyOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = factor();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression factor() {
        // Factor --> [ UnaryOp ] Primary 
        if (isUnaryOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term = primary();
            return new Unary(op, term);
        }
        else return primary();
    }
  
    private Expression primary () {
        // Primary --> Identifier | Literal | ( Expression )
        //             | Type ( Expression )
        Expression e = null;
        if (token.type().equals(TokenType.Identifier)) {
            Variable v = new Variable(match(TokenType.Identifier));
            e = v;
            if(token.type().equals(TokenType.LeftParen)) {
                token=lexer.next();
                Call c=new Call();
                c.name=v.id();
                c.args=arguments();
                match(TokenType.RightParen);
                e=c;
            }
        } else if (isLiteral()) {
            e = literal();
        } else if (token.type().equals(TokenType.LeftParen)) {
            token = lexer.next();
            e = expression();       
            match(TokenType.RightParen);
        } else if (isType( )) {
            Operator op = new Operator(match(token.type()));
            match(TokenType.LeftParen);
            Expression term = expression();
            match(TokenType.RightParen);
            e = new Unary(op, term);
        } else error("Identifier | Literal | ( | Type");
        return e;
    }

    private Value literal( ) {
        Value v = null;
        if(token.type().equals(TokenType.FloatLiteral)){
            v = new FloatValue(Float.parseFloat(token.value()));
            match(TokenType.FloatLiteral);
        }
        else if(token.type().equals(TokenType.IntLiteral)){
            v = new  IntValue(Integer.parseInt(token.value()));
            match(TokenType.IntLiteral);

        }
        else if(token.type().equals(TokenType.CharLiteral)){
            v= new CharValue((token.value().charAt(0)));
            match(TokenType.CharLiteral);
        }
        else if(token.value()== "true"){
            v = new BoolValue(true);
            match(TokenType.True);
        }
        else if(token.value() == "false"){
            v = new BoolValue(false);
            match(TokenType.False);
        }
        else
            error(token.type());

        return v;
                // student exercise
    }
  

    private boolean isAddOp( ) {
        return token.type().equals(TokenType.Plus) ||
               token.type().equals(TokenType.Minus);
    }
    
    private boolean isMultiplyOp( ) {
        return token.type().equals(TokenType.Multiply) ||
               token.type().equals(TokenType.Divide);
    }
    
    private boolean isUnaryOp( ) {
        return token.type().equals(TokenType.Not) ||
               token.type().equals(TokenType.Minus);
    }
    
    private boolean isEqualityOp( ) {
        return token.type().equals(TokenType.Equals) ||
            token.type().equals(TokenType.NotEqual);
    }
    
    private boolean isRelationalOp( ) {
        return token.type().equals(TokenType.Less) ||
               token.type().equals(TokenType.LessEqual) || 
               token.type().equals(TokenType.Greater) ||
               token.type().equals(TokenType.GreaterEqual);
    }
    
    private boolean isType( ) {
        return token.type().equals(TokenType.Int)
            || token.type().equals(TokenType.Bool) 
            || token.type().equals(TokenType.Float)
            || token.type().equals(TokenType.Char);
    }
    
    private boolean isLiteral( ) {
        return token.type().equals(TokenType.IntLiteral) ||
            isBooleanLiteral() ||
            token.type().equals(TokenType.FloatLiteral) ||
            token.type().equals(TokenType.CharLiteral);
    }
    
    private boolean isBooleanLiteral( ) {
        return token.type().equals(TokenType.True) ||
            token.type().equals(TokenType.False);
    }

    public static void main(String args[]) {
        Parser parser  = new Parser(new Lexer(args[0]));
        Program prog = parser.program();
        prog.display(0);           // display abstract syntax tree
    } //main

} // Parser
