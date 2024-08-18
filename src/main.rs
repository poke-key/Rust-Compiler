// The Rust Programming Language: A Crash Course and Building Our First Lexer
// CS152 Compiler Design using the Rust Programming Language.
// A Handwritten Compiler Using Rust.
// Creating a Lexer By Hand.

// used to get the commandline arguments from the commandline.
use std::env;
// used to interact with the file system
use std::fs;

mod interpreter;

fn main() {

  // get commandline arguments.
  let args: Vec<String> = env::args().collect();
  if args.len() == 1 {
      println!("Please provide an input file.");
      return;
  }

  if args.len() > 2 {
      println!("Too many commandline arguments.");
      return;
  }

  // read the entire file.
  let filename = &args[1];
  let result = fs::read_to_string(filename);
  let code = match result {
  Err(error) => {
      println!("**Error. File \"{}\": {}", filename, error);
      return;
  }

  Ok(code) => {
    code
  } 

  };

  let tokens = match lex(&code) {
  Err(error_message) => {
      println!("**Error**");
      println!("----------------------");
      println!("{}", error_message);
      println!("----------------------");
      return;
  }

  Ok(tokens) => tokens,
  
  };
  
  let mut index: usize = 0;
  match parse_program(&tokens, &mut index) {

    Ok(generated_code) => {
      println!("Program Parsed Successfully.\n");
      println!("----- Generated IR -----\n");
      println!("{generated_code}");
      println!("------------------------");

      interpreter::execute_ir(&generated_code);
    }

    Err(message) => {
        println!("**Error**");
        println!("----------------------");
        if tokens.len() == 0 {
            println!("No code has been provided.");
        } else {
            println!("Error: {message}");
            println!("----------------------");
        }
    }

  }
}


// Creating an Enum within Rust.
// Documentation: https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html
// Enums are a way of saying a value is one of a possible set of values.
// Unlike C, Rust enums can have values associated with that particular enum value.
// for example, a Num has a 'i32' value associated with it, 
// but Plus, Subtract, Multiply, etc. have no values associated with it.
#[derive(Debug, Clone)]
enum Token {
  NotToken,
  Plus,
  Subtract,
  Multiply,
  Divide,
  Modulus,
  Assign,
  Num(i32),
  Ident(String),
  If,
  While,
  Read, 
  Func,
  Return,
  Int,
  Continue,
  LeftParen,
  RightParen,
  LeftCurly,
  RightCurly,
  LeftBracket,
  RightBracket,
  Comma,
  Semicolon,
  Less,
  LessEqual,
  Greater,
  GreaterEqual,
  Equality,
  NotEqual,
  Print,
  Break,
  Else
}

// In Rust, you can model the function behavior using the type system.
// https://doc.rust-lang.org/std/result/
// Result < Vec<Token>, String>
// means that this function can either return:
// - A list of tokens as a Vec<Token>
// - Or an error message represented as a string
// If there is an error, it will return an error
// If successful, it will return Vec<Token>
// A Result is an enum like this:
// enum Result {
//     Ok(the_result),
//     Err(the_error),
// }

struct Expression {
  code: String,
  name: String,
}

static mut VAR_NUM: i64 = 0;

fn create_temp() -> String {
    unsafe {
        VAR_NUM += 1;
        format!("_temp{}", VAR_NUM)
    }
}

use std::collections::HashMap;

#[derive(Clone)]
enum SymbolType {
    Scalar,
    Array(i32),
}

//Symbol Table
struct Context {
    functions: HashMap<String, bool>,
}

struct Scope<'a> {
    ctx: &'a mut Context,
    variables: HashMap<String, SymbolType>,
}

impl Context {
    fn new() -> Self {
        Self {
            functions: HashMap::new(),
        }
    }

    fn add_function(&mut self, name: String) -> Result<(), String> {
        if self.functions.contains_key(&name) {
            Err(format!("Found a duplicate function '{}'", name))
        } else {
            self.functions.insert(name, true);
            Ok(())
        }
    }

    fn is_function_defined(&self, name: &str) -> Result<(), String> {
        println!("Hash Table: {:?}", self.functions);
        if self.functions.contains_key(name) {
            Ok(())
        } else {
            Err(format!("Function '{}' not defined", name))
        }
    }
}

impl <'a> Scope<'a> {
    fn new(ctx: &'a mut Context) -> Self {
        Self {
            ctx: ctx,
            variables: HashMap::new(),
        }
    }

    fn copy_from(&mut self, other: &HashMap<String, SymbolType>) {
        self.variables = other.clone();
    }

    fn add_variable(&mut self, name: String, symbol_type: SymbolType) -> Result<(), String> {
        if self.variables.contains_key(&name) {
            Err(format!("Found a duplicate variable '{}'", name))
        } else {
            self.variables.insert(name, symbol_type);
            Ok(())
        }
    }

    fn get_variable(&self, name: &str) -> Result<&SymbolType, String> {
        self.variables.get(name).ok_or(format!("Variable '{}' not declared", name))
    }
}

static mut BREAK_STACK: Vec<String> = Vec::new();
static mut CONTINUE_STACK: Vec<String> = Vec::new();

// This is a lexer that parses numbers/identifiers and math operations
fn lex(mut code: &str) -> Result<Vec<Token>, String> {
  let mut tokens: Vec<Token> = vec![];
  while code.len() > 0 {
    if code.starts_with("#") {
      while !code.starts_with('\n') {
        code = &code[1..];
      }
      code = &code[1..];
      continue;
    }

    let (success, token, rest) = lex_number(code);
    if success {
      code = rest; 
      tokens.push(token);
      continue;
    } 
 
    let (success, rest) = lex_space(code);
    if success {
      code = rest;
      continue;
    }

    if code.starts_with("+") {
      code = &code[1..];
      tokens.push(Token::Plus);
      continue;
    }

    if code.starts_with("-") {
      code = &code[1..];
      tokens.push(Token::Subtract);
      continue;
    }

    if code.starts_with("*") {
      code = &code[1..];
      tokens.push(Token::Multiply);
      continue;
    }

    if code.starts_with("/") {
      code = &code[1..];
      tokens.push(Token::Divide);
      continue;
    }

    if code.starts_with("%") {
      code = &code[1..];
      tokens.push(Token::Modulus);
      continue;
    }

    if code.starts_with("==") {
      code = &code[2..];
      tokens.push(Token::Equality);
      continue;
    }

    if code.starts_with("=") {
      code = &code[1..];
      tokens.push(Token::Assign);
      continue;
    }
    
    if code.starts_with("(") {
        code = &code[1..];
        tokens.push(Token::LeftParen);
        continue;
    }

    if code.starts_with(")") {
        code = &code[1..];
        tokens.push(Token::RightParen);
        continue;
    }

    if code.starts_with("{") {
        code = &code[1..];
        tokens.push(Token::LeftCurly);
        continue;
    }
    
    if code.starts_with("}") {
        code = &code[1..];
        tokens.push(Token::RightCurly);
        continue;
    }
    
    if code.starts_with("[") {
        code = &code[1..];
        tokens.push(Token::LeftBracket);
        continue;
    }
    
    if code.starts_with("]") {
        code = &code[1..];
        tokens.push(Token::RightBracket);
        continue;
    }

    if code.starts_with(">=") {
      code = &code[2..];
      tokens.push(Token::GreaterEqual);
      continue;
    }

    if code.starts_with("<=") {
      code = &code[2..];
      tokens.push(Token::LessEqual);
      continue;
    }

    if code.starts_with("<") {
        code = &code[1..];
        tokens.push(Token::Less);
        continue;
    }
    
    if code.starts_with(">") {
        code = &code[1..];
        tokens.push(Token::Greater);
        continue;
    }
    
    if code.starts_with("!=") {
        code = &code[2..];
        tokens.push(Token::NotEqual);
        continue;
    }
    
    if code.starts_with(";") {
        code = &code[1..];
        tokens.push(Token::Semicolon);
        continue;
    }
    
    if code.starts_with(",") {
        code = &code[1..];
        tokens.push(Token::Comma);
        continue;
    }

    let (success, token, rest) = lex_identifier(code);
    if success {
      code = rest;
      tokens.push(token);
      continue;
    }

    let symbol = unrecognized_symbol(code);
    return Err(format!("Unidentified symbol {symbol}"));

  }

  return Ok(tokens);
}

fn lex_space(code: &str) -> (bool, &str) {
  for letter in code.chars() {
    if letter.is_whitespace() {
      return (true, &code[1..]);
    } else {
      return (false, code);
    }
  }
  return (false, code);
}

// lex numbers.
fn lex_number(code: &str) -> (bool, Token, &str) {
  enum StateMachine {
    Start,
    Number,
  }

  let mut success = false;
  let mut state = StateMachine::Start;
  let mut index = 0;
  for letter in code.chars() {
    match state {
    StateMachine::Start => {
      if letter >= '0' && letter <= '9' {
        state = StateMachine::Number;
        success = true;
        index += 1;
      } else {
        return (false, Token::NotToken, "");
      }
    }

    StateMachine::Number => {
      if letter >= '0' && letter <= '9' {
        state = StateMachine::Number;
        success = true;
        index += 1;
      } 

      else if (letter >= 'A' && letter <= 'Z') || (letter >= 'a' && letter <= 'z') || (letter >= '0' && letter <= '9') || letter == '_' {
        return (false, Token::NotToken, "");
      }
      
      else {
        let num = code[..index].parse::<i32>().unwrap();
        return (true, Token::Num(num), &code[index..]);
      }
    }

    }
  }

  if success == true {
    let num: i32 = code.parse::<i32>().unwrap();
    return (true, Token::Num(num), "");
  } else {
    return (false, Token::NotToken, "");
  }
}

// lex identifiers.
fn lex_identifier(code: &str) -> (bool, Token, &str) {
  enum StateMachine {
    Start,
    Ident,
  }

  let mut success = false;
  let mut state = StateMachine::Start;
  let mut index = 0;
  for letter in code.chars() {
    match state {
    StateMachine::Start => {
      if (letter >= 'a' && letter <= 'z') || (letter >= 'A' && letter <= 'Z'){
        state = StateMachine::Ident;
        success = true;
        index += 1;
      } else {
        return (false, Token::NotToken, "");
      }
    }

    StateMachine::Ident => {
      if (letter >= 'A' && letter <= 'Z') || (letter >= 'a' && letter <= 'z') || (letter >= '0' && letter <= '9') || letter == '_' {
        state = StateMachine::Ident;
        success = true;
        index += 1;
      } else {
        let token = &code[..index];
        return (true, create_identifier(token), &code[index..]);
      }
    }

    }
  }

  if success == true {
    return (true, create_identifier(code), "");
  } else {
    return (false, Token::NotToken, "");
  }
}

fn unrecognized_symbol(code: &str) -> &str {
  enum StateMachine {
    Start,
    Symbol,
  }

  let mut state_machine = StateMachine::Start;
  let mut index = 0;
  for letter in code.chars() {
    match state_machine {
    StateMachine::Start => {
      state_machine = StateMachine::Symbol;
      index += 1;
    } 
    
    StateMachine::Symbol => {
      if letter.is_whitespace() {
        return &code[..index];
      } else {
        index += 1;
      }
    }

    }
  }
  return &code[..index];
} 

fn create_identifier(code: &str) -> Token {
    match code {
    "func" => Token::Func,
    "return" => Token::Return,
    "int" => Token::Int,
    "print" => Token::Print,
    "read" => Token::Read,
    "while" => Token::While,
    "if" => Token::If,
    "else" => Token::Else,
    "break" => Token::Break,
    "continue" => Token::Continue,
    "(" => Token::LeftParen,
    ")" => Token::RightParen,
    "{" => Token::RightCurly,
    "}" => Token::LeftCurly,
    "[" => Token::LeftBracket,
    "]" => Token::RightBracket,
    "," => Token::Comma,
    ";" => Token::Semicolon,
    "+" => Token::Plus,
    "-" => Token::Subtract,
    "*" => Token::Multiply,
    "/" => Token::Divide,
    "%" => Token::Modulus,
    "=" => Token::Assign,
    "<" => Token::Less,
    "<="=> Token::LessEqual,
    ">" => Token::Greater,
    ">="=> Token::GreaterEqual,
    "=="=> Token::Equality,
    "!="=> Token::NotEqual,
    _ => Token::Ident(String::from(code)),
    }
}


#[allow(dead_code)]
fn peek<'a>(tokens: &'a Vec<Token>, index: usize) -> Option<&'a Token> {
    if index < tokens.len() {
        return Some(&tokens[index])
    } else {
        return None
    }
}

fn peek_result<'a>(tokens: &'a Vec<Token>, index: usize) -> Result<&'a Token, String> {
    if index < tokens.len() {
        return Ok(&tokens[index])
    } else {
        return Err(String::from("expected a token, but got nothing"))
    }
}

// this 'dead_code' macro is just to supress Rust's dead_code warning. This macro can be removed.
#[allow(dead_code)]
fn next<'a>(tokens: &'a Vec<Token>, index: &mut usize) -> Option<&'a Token> {
    if *index < tokens.len() {
        let ret = *index;
        *index += 1;
        return Some(&tokens[ret])
    } else {
        return None
    }
}

fn next_result<'a>(tokens: &'a Vec<Token>, index: &mut usize) -> Result<&'a Token, String> {
    if *index < tokens.len() {
        let ret = *index;
        *index += 1;
        return Ok(&tokens[ret])
    } else {
        return Err(String::from("expected a token, but got nothing"))
    }
}

// Parse overall program
fn parse_program(tokens: &Vec<Token>, index: &mut usize) -> Result<String, String> {
  
  let mut ctx = Context::new();

  let mut ir_code: String = String::from("");
  loop {
      match parse_function(tokens, index, &mut ctx)? {
          None => break,
          Some(function_code) => {
              ir_code += &function_code;
          }
      }
  }
  if !ir_code.contains("%func main()") {
    return Err(String::from("'main' function not defined"));
  }
  return Ok(ir_code);
}

//Parse statement
fn parse_statement(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Option<String>, String> {
    let mut statement_code: String = String::from("");
 
    match peek_result(tokens, *index)? {
        Token::RightCurly => return Ok(None),
 
        Token::Int => {
            match parse_declaration(tokens, index, scope)? {
                None => return Ok(None),
                Some(declaration_code) => {
                    statement_code += &declaration_code;
                }
            }
        }
 
        Token::Ident(ident) => {
            *index += 1;
        
            // Check if the variable has been declared before use
            let symbol_type = match scope.get_variable(ident) {
                Ok(symbol_type) => symbol_type,
                Err(_) => return Err(format!("Variable '{}' not declared", ident)),
            };
        
            match peek_result(tokens, *index)? {
                // handle array assignment
                Token::LeftBracket => {
                    match symbol_type {
                        SymbolType::Array(_) => {
                            *index += 1;
                            let index_expr = parse_expression(tokens, index, scope)?;
                            if !matches!(next_result(tokens, index)?, Token::RightBracket) {
                                return Err(String::from("expect ']' closing array index"));
                            }
                            if !matches!(peek_result(tokens, *index)?, Token::Assign) {
                                return Err(String::from("expect '=' after array index"));
                            }
                            *index += 1;
                            let value_expr = parse_expression(tokens, index, scope)?;
                            statement_code += &format!("{}{}%mov [{} + {}], {}\n", index_expr.code, value_expr.code, ident, index_expr.name, value_expr.name);
                        }
                        _ => return Err(format!("Type mismatch: '{}' is not an array", ident)),
                    }
                }
        
                // handle assignment
                Token::Assign => {
                    match symbol_type {
                        SymbolType::Scalar => {
                            *index += 1;
                            let expr = parse_expression(tokens, index, scope)?;
                            statement_code += &format!("{}%mov {}, {}\n", expr.code, ident, expr.name);
                        }
                        _ => return Err(format!("Type mismatch: '{}' is an array", ident)),
                    }
                }
        
                // handle function call
                Token::LeftParen => {
                    
                    scope.ctx.is_function_defined(ident)?;

                    *index += 1;
                    let mut args_code = String::new();
                    let mut args = Vec::new();
        
                    loop {
                        match peek_result(tokens, *index)? {
                            Token::Comma => {
                                *index += 1;
                            }
                            Token::RightParen => {
                                *index += 1;
                                break;
                            }
                            _ => {
                                let arg = parse_expression(tokens, index, scope)?;
                                args_code += &arg.code;
                                args.push(arg.name);
                            }
                        }
                    }
        
                    let temp = create_temp();
                    statement_code += &format!("%int {}\n", temp);
                    statement_code += &format!("{}%call {}, {}({})\n", args_code, temp, ident, args.join(", "));
                }
        
                _ => return Err(String::from("expected '=' or '(' or '[' after identifier")),
            }
        }
 
        Token::Print => {
            *index += 1;
            if !matches!(next_result(tokens, index)?, Token::LeftParen) {
                return Err(String::from("expect '(' closing statement"));
            }
            let expr = parse_expression(tokens, index, scope)?;
            statement_code += &format!("{}%out {}\n", expr.code, expr.name);
            if !matches!(next_result(tokens, index)?, Token::RightParen) {
                return Err(String::from("expect ')' closing statement"));
            }
        }
 
        Token::Read => {
            *index += 1;
            if !matches!(next_result(tokens, index)?, Token::LeftParen) {
                return Err(String::from("expect '(' closing statement"));
            }
            let expr = parse_expression(tokens, index, scope)?;
            statement_code += &format!("{}%input {}\n", expr.code, expr.name);
            if !matches!(next_result(tokens, index)?, Token::RightParen) {
                return Err(String::from("expect ')' closing statement"));
            }
        }
 
        Token::Return => {
            *index += 1;
            let expr = parse_expression(tokens, index, scope)?;
            statement_code += &format!("{}%ret {}\n", expr.code, expr.name);
        }

        Token::While => {
            match parse_while_statement(tokens, index, scope)? {
                Some(while_code) => {
                    statement_code += &while_code;
                }
                _ => {
                    return Err(String::from("Invalid While Code"))
                }
            }

           return Ok(Some(statement_code))
        }

        Token::If => {
            match parse_if_statement(tokens, index, scope)? {
                Some(if_code) => {
                    statement_code += &if_code;
                }
                _ => {
                    return Err(String::from("Invalid If Code"))
                }
            }

            return Ok(Some(statement_code))
        }

        Token::Break => {
            *index += 1;
            unsafe {
                if BREAK_STACK.is_empty() {
                    return Err(String::from("break used outside loop"))
                }
                statement_code += &format!("%jmp :end{}\n", BREAK_STACK.last().unwrap());
                BREAK_STACK.pop();
            }
        }

        Token::Continue => {
            *index += 1;
            unsafe {
                if CONTINUE_STACK.is_empty() {
                    return Err(String::from("continue used outside loop"))
                }
                statement_code += &format!("%jmp :{:#?}\n", CONTINUE_STACK.last().unwrap());
                CONTINUE_STACK.pop();
            }
        }
 
        _ => return Err(String::from("invalid statement.")),
    }
 
    if !matches!(next_result(tokens, index)?, Token::Semicolon) {
        return Err(String::from("expect ';' closing statement"));
    }
 
    return Ok(Some(statement_code))
}


// Parse declaration
fn parse_declaration(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Option<String>, String> {
    match next_result(tokens, index)? {
        Token::Int => {},
        _ => return Err(String::from("declarations must begin with 'int'")),
    }

    let mut declaration_code = String::new();
    let mut ident = String::new();

    match next_result(tokens, index)? {
        Token::Ident(id) => {
            if scope.variables.contains_key(id) {
                return Err(format!("Found a duplicate variable '{}'", id));
            }
            scope.add_variable(id.clone(), SymbolType::Scalar)?;
            declaration_code += &format!("%int {}\n", id);
            ident = id.to_string();
        },

        Token::LeftBracket => {
            let size = match next_result(tokens, index)? {
                Token::Num(size) => size,
                _ => return Err(String::from("expected a number inside brackets")),
            };

            if *size <= 0 {
                return Err(String::from("Array size must be greater than 0"));
            }

            if !matches!(next_result(tokens, index)?, Token::RightBracket) {
                return Err(String::from("missing ']'"));
            }

            let id = match next_result(tokens, index)? {
                Token::Ident(id) => id,
                _ => return Err(String::from("expected an identifier after ']'")),
            };

            if scope.variables.contains_key(id) {
                return Err(format!("Found a duplicate variable '{}'", id));
            }

            scope.add_variable(id.clone(), SymbolType::Array(*size))?;
            declaration_code += &format!("%int[] {}, {}\n", id, size);
            ident = id.to_string();

            if matches!(peek_result(tokens, *index)?, Token::Assign) {
                return Err(format!("cannot initialize an array immediately"));
            }
        }
        _ => return Err(String::from("expected an identifier after 'int'")),
    };

    if matches!(peek_result(tokens, *index)?, Token::Assign) {
        *index += 1;
        // Handle variable assignment
        let expr = parse_expression(tokens, index, scope)?;
        declaration_code += &expr.code;
        declaration_code += &format!("%mov {}, {}\n", ident, expr.name);
    }

    Ok(Some(declaration_code))
}


// Parse function
fn parse_function(tokens: &Vec<Token>, index: &mut usize, ctx: &mut Context) -> Result<Option<String>, String> {
  match next(tokens, index) {
      None => return Ok(None),
      Some(token) => {
          if !matches!(token, Token::Func) {
              return Err(String::from("functions must begin with func"));
          }
      }
  }

  let mut function_code = String::new();
  let mut parameters: Vec<String> = Vec::new();
  let mut function_name = String::new();

  match next_result(tokens, index)? {
      Token::Ident(ident) => {
        function_name = ident.clone();
        ctx.add_function(ident.to_string())?;
      },
      _ => return Err(String::from("functions must have a function identifier")),
  }

  if !matches!(next_result(tokens, index)?, Token::LeftParen) {
      return Err(String::from("expected '('"));
  }

  let mut scope = Scope::new(ctx);

  loop {
      match next_result(tokens, index)? {
          Token::RightParen => break,
          Token::Int => {
              match next_result(tokens, index)? {
                  Token::Ident(ident) => {
                      // Add parameters to the local symbol table
                      scope.add_variable(ident.clone(), SymbolType::Scalar)?;
                      parameters.push(ident.clone());

                      match peek_result(tokens, *index)? {
                          Token::Comma => {
                              *index += 1;
                          }
                          Token::RightParen => {}
                          _ => return Err(String::from("expected ',' or ')'")),
                      }
                  }
                  _ => return Err(String::from("expected ident function parameter")),
              }
          }
          _ => return Err(String::from("expected 'int' keyword or ')' token")),
      }
  }

  function_code += &format!("%func {}(", function_name);
  for param in &parameters {
      function_code += &format!("%int {}, ", param);
  }
  function_code += ")\n";

  if !matches!(next_result(tokens, index)?, Token::LeftCurly) {
      return Err(String::from("expected '{'"));
  }
  
  loop {
      match parse_statement(tokens, index, &mut scope)? {
          None => break,
          Some(statement) => function_code += &statement,
      }
  }

  function_code += "%endfunc\n";

  if !matches!(next_result(tokens, index)?, Token::RightCurly) {
      return Err(String::from("expected '}'"));
  }

  Ok(Some(function_code))
}
 

fn parse_while_statement(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Option<String>, String> {

    let mut while_code = String::new();
    
    if !matches!(next_result(tokens, index)?, Token::While) {
        return Err(String::from("while loop must begin with While"));
    }

    let condition_expr = parse_bool_expression(tokens, index, scope)?;

    if !matches!(next_result(tokens, index)?, Token::LeftCurly) {
        return Err(String::from("expected '{'"));
    }

    // Create a new scope for the while block
    let mut while_scope = Scope::new(scope.ctx);
    while_scope.copy_from(&scope.variables);

    let label = create_temp();
    unsafe {
        BREAK_STACK.push(label.to_string());
        CONTINUE_STACK.push(label.to_string());
    }

    while_code += &format!(":{}\n", label);
    while_code += &condition_expr.code;
    
    while_code += &format!("%branch_ifn {}, :end{}\n", condition_expr.name, label);

    loop {
        match parse_statement(tokens, index, &mut while_scope)? {
            None => break,
            Some(statement_code) => while_code += &statement_code,
        }
    }

    while_code += &format!("%jmp :{}\n", label);
    while_code += &format!(":end{}\n", label);

    if !matches!(next_result(tokens, index)?, Token::RightCurly) {
        return Err(String::from("expected '}'"));
    }

    Ok(Some(while_code))
}

fn parse_if_statement(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Option<String>, String> {
    if !matches!(next_result(tokens, index)?, Token::If) {
        return Err(String::from("if statement must begin with If"));
    }

    let condition_expr = parse_bool_expression(tokens, index, scope)?;

    if !matches!(next_result(tokens, index)?, Token::LeftCurly) {
        return Err(String::from("expected '{'"));
    }

    let label = create_temp();
    let mut if_code = String::new();
    if_code += &condition_expr.code;
    if_code += &format!("%branch_ifn {}, :else{}\n", condition_expr.name, label);

    // Create a new scope for the if block
    let mut if_scope = Scope::new(scope.ctx);
    if_scope.copy_from(&scope.variables);

    loop {
        match parse_statement(tokens, index, &mut if_scope)? {
            None => break,
            Some(statement_code) => if_code += &statement_code,
        }
    }

    if_code += &format!("%jmp :endif{}\n", label);
    if_code += &format!(":else{}\n", label);

    if !matches!(next_result(tokens, index)?, Token::RightCurly) {
        return Err(String::from("expected '}'"));
    }

    match peek_result(tokens, *index)? {
        Token::Else => {
            *index += 1;
            if !matches!(next_result(tokens, index)?, Token::LeftCurly) {
                return Err(String::from("expected '{'"));
            }

            // Create a new scope for the else block
            let mut else_scope = Scope::new(scope.ctx);
            else_scope.copy_from(&scope.variables);

            loop {
                match parse_statement(tokens, index, &mut else_scope)? {
                    None => break,
                    Some(statement_code) => if_code += &statement_code,
                }
            }

            if !matches!(next_result(tokens, index)?, Token::RightCurly) {
                return Err(String::from("expected '}'"));
            }
        }
        _ => {}
    }

    if_code += &format!(":endif{}\n", label);

    Ok(Some(if_code))
}


// Parse boolean expression
fn parse_bool_expression(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Expression, String> {
    let expr1 = parse_expression(tokens, index, scope)?;

    let comparison = match next_result(tokens, index)? {
        Token::Less => "lt",
        Token::LessEqual => "le",
        Token::Greater => "gt",
        Token::GreaterEqual => "ge",
        Token::Equality => "eq",
        Token::NotEqual => "neq",
        _ => return Err(String::from("Expected a comparison operator")),
    };

    let expr2 = parse_expression(tokens, index, scope)?;

    let temp = create_temp();
    let mut bool_code = String::new();
    bool_code += &format!("{}{}%int {}\n", expr1.code, expr2.code, temp);
    bool_code += &format!("%{} {}, {}, {}\n", comparison, temp, expr1.name, expr2.name);

    Ok(Expression { name: temp, code: bool_code })
}

// Parse expression
fn parse_expression(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Expression, String> {
  let mut name = parse_multiply_expression(tokens, index, scope)?;

  loop {
      match peek_result(tokens, *index)? {
          Token::Plus => {
              *index += 1;
              let right = parse_multiply_expression(tokens, index, scope)?;
              let temp = create_temp();
              name.code += &format!("%int {}\n", temp);
              name.code += &format!("{}%add {}, {}, {}\n", right.code, temp, name.name, right.name);
              name = Expression { code: name.code, name: temp };
          }
          Token::Subtract => {
              *index += 1;
              let right = parse_multiply_expression(tokens, index, scope)?;
              let temp = create_temp();
              name.code += &format!("%int {}\n", temp);
              name.code += &format!("{}%sub {}, {}, {}\n", right.code, temp, name.name, right.name);
              name = Expression { code: name.code, name: temp };
          }
          _ => break,
      }
  }

  Ok(name)
}

// Parse multiply expression
fn parse_multiply_expression(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Expression, String> {
  let mut name = parse_term(tokens, index, scope)?;

  loop {
      match peek_result(tokens, *index)? {
          Token::Multiply => {
              *index += 1;
              let right = parse_term(tokens, index, scope)?;
              let temp = create_temp();
              name.code += &format!("%int {}\n", temp);
              name.code += &format!("{}%mult {}, {}, {}\n", right.code, temp, name.name, right.name);
              name = Expression { code: name.code, name: temp };
          }
          Token::Divide => {
              *index += 1;
              let right = parse_term(tokens, index, scope)?;
              let temp = create_temp();
              name.code += &format!("%int {}\n", temp);
              name.code += &format!("{}%div {}, {}, {}\n", right.code, temp, name.name, right.name);
              name = Expression { code: name.code, name: temp };
          }
          Token::Modulus => {
              *index += 1;
              let right = parse_term(tokens, index, scope)?;
              let temp = create_temp();
              name.code += &format!("%int {}\n", temp);
              name.code += &format!("{}%mod {}, {}, {}\n", right.code, temp, name.name, right.name);
              name = Expression { code: name.code, name: temp };
          }
          _ => break,
      }
  }

  Ok(name)
}

// Parse term
fn parse_term(tokens: &Vec<Token>, index: &mut usize, scope: &mut Scope) -> Result<Expression, String> {
  match next_result(tokens, index)? {
      Token::Num(num) => Ok(Expression { code: String::new(), name: num.to_string() }),

      Token::LeftParen => {
          let expr = parse_expression(tokens, index, scope)?;
          if !matches!(next_result(tokens, index)?, Token::RightParen) {
              return Err(String::from("expected ')' parenthesis"));
          }
          Ok(expr)
      }

      Token::Ident(ident) => {

          match peek_result(tokens, *index)? {
              
              // function call
              Token::LeftParen => {

                scope.ctx.is_function_defined(ident)?;

                *index += 1;
                let mut args_code = String::new();
                let mut args = Vec::new();

                loop {
                    match peek_result(tokens, *index)? {
                        Token::Comma => {
                            *index += 1;
                        }
                        Token::RightParen => {
                            *index += 1;
                            break;
                        }
                        _ => {
                            let arg = parse_expression(tokens, index, scope)?;
                            args_code += &arg.code;
                            args.push(arg.name);
                        }
                    }
                }

                let temp = create_temp();
                let mut call_code = format!("");
                call_code += &format!("%int {}\n", temp);
                call_code += &format!("{}%call {}, {}({})\n", args_code, temp, ident, args.join(", "));
                Ok(Expression { code: call_code, name: temp })
              }

              // array access
              Token::LeftBracket => {

                let symbol_type = match scope.get_variable(&ident) {
                    Ok(symbol_type) => symbol_type,
                    Err(_) => return Err(format!("Variable '{}' not declared", ident)),
                };

                match symbol_type {
                    SymbolType::Array(_) => {
                        *index += 1;
                        let index_expr = parse_expression(tokens, index, scope)?;
                        if !matches!(next_result(tokens, index)?, Token::RightBracket) {
                            return Err(String::from("expected ']' bracket"));
                        }
                        let temp = create_temp();
                        let mut code = format!("");
                        code += &format!("%int {}\n", temp);
                        code += &format!("{}%mov {}, [{} + {}]\n", index_expr.code, temp, ident, index_expr.name);
                        Ok(Expression { code, name: temp })
                    }

                    _ => return Err(format!("Type mismatch: '{}' is not an array", ident)),
                }
              }

              // just the identifier itself
              _ => {

                let symbol_type = match scope.get_variable(&ident) {
                    Ok(symbol_type) => symbol_type,
                    Err(_) => return Err(format!("Variable '{}' not declared", ident)),
                };

                match symbol_type {
                    SymbolType::Scalar => {
                        Ok(Expression { code: String::new(), name: ident.to_string() })
                    },
                    _ => return Err(format!("Type mismatch: '{}' is an array", ident)),
                }
            },
        }
    },

    _ => Err(String::from("invalid expression")),
  }
}


//HELPER / TEST FUNCTION; not necessary for the parser

// fn parse_math(tokens: &Vec<Token>, index: &mut usize) -> Result<i32, String> {
//   let answer = parse_expression(tokens, index)?;
//   if matches!(next_result(tokens, index)?, Token::Semicolon) {
//     return Ok(answer);
//   } else {
//     return Err(String::from("missing semicolon ';'"));
//   }
// }


// writing tests!
// testing shows robustness in software, and is good for spotting regressions
// to run a test, type "cargo test" in the terminal.
// Rust will then run all the functions annotated with the "#[test]" keyword.
// #[cfg(test)]
// mod tests {
//     use crate::lex;
//     use crate::parse_statement;

//     #[test]
//     fn test_statements() {

//         // test that valid statements are correct.
//         let tokens = lex("a = 1 + 2;").unwrap();
//         parse_statement(&tokens, &mut 0, ).unwrap();

//         let tokens = lex("b = 1 / 2;").unwrap();
//         parse_statement(&tokens, &mut 0).unwrap();


//         // test errors. missing semicolon
//         let tokens = lex("b = 1 / 2").unwrap();
//         assert!(matches!(parse_statement(&tokens, &mut 0), Err(_)));

//     }

// }