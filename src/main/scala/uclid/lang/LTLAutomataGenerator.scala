/*
 * UCLID5 Verification and Synthesis Engine
 *
 * Copyright (c) 2017.
 * Sanjit A. Seshia, Rohit Sinha and Pramod Subramanyan.
 *
 * All Rights Reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *
 * this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 *
 * documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from this
 * software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Author: Ofek Shani
 *
 * Compute the GNBA's correspoinding to each LTL formula in a module and combine them in lockstep with the TS
 * 
 * This approach is based on the automata-theoretic approach to LTL verification. Process is as follows:
 * For each LTL formula in the inputted Transition System (TS), construct a Generalized Nondeterministic Buchi Automata
 * (GNBA) representing its negation (aka a GNBA for the formula's forbidden cases). 
 * Then, run that formula in lockstep with the TS (here we combine the modules).
 * If both modules accept, then there exists a trace that satisfies the TS AND contains a forbidden case by the formula. 
 *
 */
package uclid
package lang

import com.typesafe.scalalogging.Logger
// below imports are necessary for spot string conversion function
import scala.collection.mutable.Stack 
import scala.collection.mutable.ArrayBuffer
import scala.sys.process._
import scala.util.parsing.combinator._
import scala.util.matching.Regex

/** 
 * In order to construct the GNBA of a formula, we use the external tool "Spot" https://spot.lre.epita.fr/
 * Specifially we use the LTL2TGBA command provided by it. 
*/
object SpotInterface {

  // list of all characters which require the surrounding area to be quoted
    // TODO: figure out if '-' is actually valid -- if so it will need to be handled differently. 
    val forbiddenChars = "+-/*%<>=".toCharArray()
    /**
      * returns an intervals of tuples describing ranges of a single parenthesis set.
      * returns tuple(int, int, int), where int 1 is index of openChar instance, int 2 is index of closeChar,
      * and int 3 is absolute depth
      * 
      * Mostly serves as a utility function for rewriteFormulaForSpot
      */ 
    def getParenRanges(string: String, openChar: Char, closeChar: Char): ArrayBuffer[(Int, Int, Int)] = {
      // TODO: Stack is depreicated -- replace this with ArrayDeque and change pop/push methods accordingly. 
      var openIndices = Stack[Int]()
      // the tuple stores index of '(', index of ')', and the depth of the pair
      var pairIndices = ArrayBuffer[(Int, Int, Int)]()
      // First, build a collection of all parenthesis pairs in the set. 
      for(i <- 0 until string.length) {
        if(string(i) == openChar) {
          openIndices.push(i)
        }
        else if(string(i) == closeChar) {
          val oIndex = openIndices.pop()
          val depth = openIndices.length

          pairIndices += ((oIndex, i, depth))
        }
      }
      return pairIndices
    }
  /**
   * prepare a given LTL formula string for use by spot by wrapping the contents of any parentheses pair in quotes if the content
   * contains a character that Spot would not be able to handle (ie, any comparison or arithmatic operators, as well as []).
   * For now we will default to any NON-alphanumeric character (except "()").
   * 
   * Why do this? Spot only supports boolean operators and literals, but UCLID lets us input expressions that evaluate to
   *  boolean values. We need to find those expressions and encase them in strings so that Spot can treat them as just a variable.
   * 
   * TODO: Spot does have a "lenient mode" that could do some of this. However it would treat some UCLID5 symbols 
   *  differently to how we want to evaluate them in UCLID (ie, treating + as conjunction rather than addition).
   *  This quote inserttion method is sloppy -- if there is a way to use SPOT directly it would be better
   * ALTERNATE TODO: Instead of traversing a string and scanning for chars, we could search the AST directly,
   *  search for operator applications of non-boolean ops, and then use that to determine whether to encase the expression in strings
  */
  def rewriteFormulaForSpot(formula: String): String = {
    /**  Process is as follows:
      *  1: get a list of all parentheses and their depths
      *  2: sort parentheses pairs in order of ascending depth
      *  3: For each pair, iterate over all chars in the range.
      *     - keep track of local depth variable
      *     - if there exists forbidden character at 0 local depth, add paren indices to "needs quotes" list
      *  4: construct the new string by iterating through the old one and inserting new quotes as need be.
      */
    val pPairIndices = getParenRanges(formula, '(',')')
    val bPairIndices = getParenRanges(formula, '[',']')

    // sort the pairs from outermost to innermost (ascending depth order).
    // If we find a non-boolean operator in one depth level, that means that all other expressions in deeper
    // levels will need to be in the quote too, so we move from shallow to deep depths.
    val sortedIndices = pPairIndices.sortBy(_._3)
    // we need to keep track of already quoted ranges so we do not put quotes inside of quotes.
    // we could technically refactor the system to use a parenthesis tree to not need this.
    var quotedRanges = ArrayBuffer[(Int, Int)]()
    var insertIndices = ArrayBuffer[Int]() // indices at which to insert double quotes (we insert before the char)
    for((openIndex, closedIndex, depth) <- sortedIndices) {
      // check to see if we're in an already quoted region. If we are, skip checking this set.
      val isInsideQuoted: Option[(Int, Int)] = quotedRanges.find {
        case ((otherOpen, otherClosed)) => otherOpen < openIndex && otherClosed > closedIndex
      }
      if(isInsideQuoted.isEmpty) { // ie, if we are in an unquoted region
        // Check to see if the range needs to be quoted. If we ever need to change the 
        // logic for HOW we decide to quote something out, this is where that change needs to be made. 
        var localDepth: Int = 0
        var hasForbiddenChar = false
        var isVector = closedIndex < formula.length -1 && formula(closedIndex+1)=='[' // is ) followed by [
        for(i <- openIndex + 1 until closedIndex) {
          val charToEval: Char = formula(i)
          if(charToEval == '(') localDepth+=1
          else if(charToEval == ')') localDepth-=1
          // we only want to check for forbidden characters at our current depth.
          hasForbiddenChar = localDepth == 0 && forbiddenChars.contains(formula(i))
        }
        if(hasForbiddenChar || isVector) {
          val newOpen = if (isVector) openIndex else openIndex + 1
          var newClosed = closedIndex
          if(isVector) {
            // find the closing ] to the [ following this paren set
            while(newClosed < formula.length -1 && formula(newClosed+1)=='[') {
              // keep searching for the next ] as long as a [ is right after our range
              newClosed = bPairIndices.find(p=> p._1 == newClosed+1).map(_._2).getOrElse(formula.length)
            }
            newClosed += 1 // we need to put the quote after the final ]
          }
          insertIndices += newOpen
          insertIndices += newClosed
          quotedRanges += ((newOpen, newClosed))
        }
      }
    }
    // Now that we know where to insert quotes, create the new string
    val sortedInsertIndices = insertIndices.sorted
    val toReturn = new StringBuilder()
    var insertionPointer = 0
    // length +1 is so that we add any necessary quotes at the end of the string
    for(i <- 0 until formula.length + 1) {
      // as long as we have quotes to print, do those
      while(insertionPointer < sortedInsertIndices.length && sortedInsertIndices(insertionPointer) == i) {
        toReturn.append('\"')
        insertionPointer += 1
      }
      // only add the original formula's character until all necessary preceeding quotes have been added.
      if(i < formula.length) {
        toReturn.append(formula(i))
      }
    }
    // ta da
    return toReturn.result()
  }


  /**
   * returns the HOA representation of a TGBA created from the LTL formula in the inputted Expression. 
   * Output is in the form of a string following the HOA format (see https://spot.lre.epita.fr/oaut.html for details)
   */
  def runLTL2TGBA(formula: Expr): String = {

    val spotFormula = rewriteFormulaForSpot(formula.toString())
    val spotCommand: Seq[String] = Seq("ltl2tgba", "-B", "-f", spotFormula)
    val processBuilder: ProcessBuilder = spotCommand
    val toReturn: String = processBuilder.!!
    return toReturn
  }
}

class LTLAutomataGeneratorPass extends RewritePass {
  
  override def rewriteModule(module: Module, ctx: Scope): Option[Module] = {
    val moduleSpecs = module.decls.collect{ case spec : SpecDecl => spec }
    val ltlSpecs = moduleSpecs.filter(s => ExprDecorator.isLTLProperty(s.params))
    val toReturn = createModulefromHOA(module, ltlSpecs(0))
    if (ltlSpecs.size == 0) {
      Some(module)
    } else {
      return Some(module)
    }
  }

  /** 
   * A small scale parser designed to turn a Spot conditional to a BlockStmt we can use in Next Block
   * label-expr ::= BOOLEAN | INT | ANAME | "!" label-expr
           | "(" label-expr ")"
            | label-expr "&" label-expr
            | label-expr "|" label-expr
    * atomics is the list of AP vars used by the module
  */
  class SpotCondMiniParser(atomics: Array[Expr]) extends RegexParsers {
    override val whiteSpace: Regex = """[ ]+""".r
    val unsigInt: Regex = """[0-9]+""".r

    private def boolLit: Parser[Expr] = ("t"|"f") ^^ {b => BoolLit(b=="t")}

    // translate numeric values to corresponding atomics
    private def intAtom : Parser[Expr] = unsigInt ^^ { num => 
      val idx = num.toInt
      if(idx > -1 && idx < atomics.length) atomics(idx)
      else sys.error(s"AP number $num not declared in AP: Line")
    }

    // recall precedence is ! > () > & > | 
    // handle !, ()
    private def atom: Parser[Expr] = 
      "!" ~> atom ^^ {e=> Operator.not(e)} |
      "(" ~> expr <~ ")" | intAtom | boolLit

    // & operator
    private def conj: Parser[Expr] = 
      rep1sep(atom, "&") ^^ {_.reduceLeft(Operator.and)}
    // | operator
    private def expr: Parser[Expr] =
      rep1sep(conj, "|") ^^ {_.reduceLeft(Operator.or)}

    def parse(condition: String) : Expr = {
      parseAll(expr, condition) match {
        case this.Success(res, _) => res
        case this.NoSuccess(msg, next) =>
          sys.error(s"parse error at ${next.pos}: $msg")
      }
    }
  }

  /** Utility that converts a string containing exactly one UCLID-5
  * expression into the corresponding AST node (`Expr`).
  *
  * Throws `Utils.SyntaxError` if the text is not a legal expression.
  * WARNING/TODO: This is an AI-written function. It still needs to be checked.
  */
  object ExprParser {
    def apply(text: String,
              fileName: String = "<input>"): Expr = {

      /* 1. Tokenise the input with the lexical analyser that already
      *    belongs to UclidParser.  Note the required `new` in front of
      *    `lexical.Scanner`.                                           */
      val scanner = new UclidParser.lexical.Scanner(text)

      /* 2. Packrat combinators need a `PackratReader`.                  */
      val tokens  = new UclidParser.PackratReader(scanner)

      /* 3. Parse the complete token stream with the `Expr` non-terminal
      *    (`phrase` insists that the whole input is consumed).         */
      UclidParser.phrase(UclidParser.Expr)(tokens) match {
        case UclidParser.Success(ast, _) => ast               // <- the Expr
        case UclidParser.NoSuccess(msg, next) =>
          throw new Utils.SyntaxError(msg, Some(next.pos), Some(fileName))
      }
    }
  }

  /**
   * Class containing the raw state, conditional, and transition data used to make the automata.
   * Note: A lot of the stuff here is generated through manual string processing. HOA has an official 
   * spec containing its regular grammer -- this could be reworked to fully user parsers for it 
   * 
   */
  class HOAData(module: Module, spotTGBA: String) {
    private val metadata = spotTGBA.split("--BODY--\n", 2)(0)
    private val metadataLines = metadata.split('\n')
    private val body = spotTGBA.split("--BODY--\n", 2)(1)
    
    // the number of states in the automata
    val numStates: Option[Int] = getDataFromField("States").map(_.toInt)

    // the initial state for the automata
    val initialStates: Option[Set[Int]] = getDataFromField("Start").map( statesStr => 
      statesStr.split("&").map(_.toInt).toSet 
    )
    
    // Array of AP's that the automata uses
    // TODO: Make sure you can actually split the strings this way -- this seems off
    val atomicExpressions: Option[Array[Expr]] = getDataFromField("AP").map( apStr => {
      // split into individual AP strings -- at this point each AP in the string is surrounded by quotes
      val strs = apStr.split(" ", 2)(1)
      // split into individual AP's by splitting by quotes and filtering out empty strings
      val noQuotes = strs.split("\"").filter(s => !s.equals(" ") && !s.equals(""))
      noQuotes.map(ExprParser(_))
    })

    // A set of all variable Identifers in the TS module that are used by the AP's
    // to obtain: extract all of the variavles in the atomics, and get their types from the module, create all the var decls for them
    val moduleVarIdentifiers = atomicExpressions.map(_.map(getIdentifiersInExpression(_))).map(_.reduce(_ union _))
    
    private val transStrings: Array[String] = body.dropRight(8).split("State: ").filter(_ != "")

    // An array of all acceptance sets for the GNBA. Recall that each acc set must be visited infinite for the 
    // automata module to accept
    val acceptSets: Option[Array[Set[Int]]] = getDataFromField("Acceptance").map( asc => {
      // Acceptance field is in the form "[#acceptsets] [acceptconds]", so we isolate the number
      var sets = Array.fill(asc.split(" ")(0).toInt)(Set[Int]())
      transStrings.foreach(s => {
        val lines = s.split('\n')
        // get state num
        val stateNum = lines(0).split(" ")(0).toInt
        // state header is [statenum] {acc_set_1 acc_set_2 ...} -- the {} only appears if there are any sets it's a part of
        val setsWithState = if(lines(0).contains('{')) 
          lines(0).split(" ", 2)(1) // isolate {...}
            .filter(c=> !("{}".contains(c))) // remove {, }
            .split(" ") // turn into arr
            .map(_.toInt) 
        else Array[Int]()
        setsWithState.foreach(aSet => sets(aSet) += stateNum)
      })
      sets
    })

    private val spotParser = atomicExpressions.map( aIds => new SpotCondMiniParser(aIds))

    /**
      * The transition function -- A list of the lists of transitions (Expr representing requirement and List[int] representing sets of destination states) for each state
      * Each transition consists of the condition required, as well as the set of states that transition connects to
      */
    val transitionsRaw: Option[List[List[(Expr, List[Int])]]] = spotParser.map{parser => 
      transStrings.zipWithIndex.toList.map{ case(str, idx) => 
        // isolate all non-header lines of the state. Each line contains a condition and the states to go to if that condition is met.
        val lines = str.split('\n').drop(1)
        // set up list of transitions for the current state
        val pairList: List[(Expr, List[Int])] = lines.toList.map{ s => 
          val condStr: String = s.slice(s.indexOf('[') + 1, s.indexOf(']'))
          val condExpr: Expr = parser.parse(condStr)
          val destinationStateStrings: List[String] = s.substring(s.indexOf(']') + 1).split(" ").toList.filter(!_.isEmpty())
          val destinationStates: List[Int] = destinationStateStrings.map(_.toInt)
          val listElt: (Expr, List[Int]) = ((condExpr, destinationStates))
          listElt
        }
        pairList
      }
    }

    // returns the data string of metadataLines at a certain field
    def getDataFromField(toFind: String): Option[String] = {
      val lineIndex = metadataLines.find(_.split(":")(0)==toFind)
      val toReturn = lineIndex.map(_.split(": ", 2)(1))
      return toReturn
    }

    /**
     * Traverses the given expression and returns all Identifiers found within as a set.
     * TODO: This function needs testing to ensure that it fully works -- I had to rely on AI heavily to implement it...
     */
    def getIdentifiersInExpression(e: Expr): Set[Identifier] = {
      def go(exp: Expr): Set[Identifier] = exp match {
        /* literals */
        case _: Literal                           => Set.empty
        /* plain identifier ------------------------------------------------ */
        case id @ Identifier(_)                     => Set(id)
        case ExternalIdentifier(_, id)              => Set(id)

        /* quantifiers (forall/exists) ------------------------------------ */
        case OperatorApplication(ForallOp(vs, _), List(arg)) =>
          go(arg) -- vs.map(_._1)                    // handled *before* generic OA
        case OperatorApplication(ExistsOp(vs, _), List(arg)) =>
          go(arg) -- vs.map(_._1)

        /* operator / function application -------------------------------- */
        case OperatorApplication(_, args)           => args.flatMap(go).toSet
        case FuncApplication(fun, args)             => go(fun) ++ args.flatMap(go)

        /* tuples, arrays, records ---------------------------------------- */
        case Tuple(elems)                           => elems.flatMap(go).toSet
        case ConstArray(defVal, _)                  => go(defVal)
        case ConstRecord(fields)                    =>
          fields.flatMap { case (_, v) => go(v) }.toSet

        /* let / lambda — remove bound names ------------------------------ */
        case LetExpr(defs, body) =>
          val bound = defs.map(_._1.asInstanceOf[Identifier]).toSet
          defs.flatMap { case (_, rhs) => go(rhs) }.toSet ++ go(body) -- bound

        case Lambda(params, body) =>
          go(body) -- params.map(_._1)        
      }

      go(e)
    }

    
  }

  def createModulefromHOA(module: Module, spec: SpecDecl): Option[Module] = {

    val spotTGBA: String = SpotInterface.runLTL2TGBA(spec.expr)

    // Top level process is as follows:
    // 0: parse HOA format -- isolate substrings with info on states, transitions, acceptance, etc
    // 1: Create the state variable declarations (will be list of BooleanTypes, since Spot only deals with bools)
    // 2: Define the init block using InitDecl (just define the inital states for all bools)
    // 3: Create the next block using NextDecl (use the transition portion of Spot Output)
    // 4: assemble the module

    // Step 0 -- we do this using the HOAData class.
    val hoaData = new HOAData(module, spotTGBA)

    /**
      * 1: Define the state and input variables, function imports, constant decls, etc.
      */
    
    // Tool for getting the types of a var in a module given its identifier. 
    // used in order to get all of the imported elements needed in the automata module
    object VariableIdentifier {
      // these are the possible types that need to be handled
      sealed trait SymbolKind
      case object Input        extends SymbolKind
      case object Output       extends SymbolKind
      case object StateVar     extends SymbolKind
      case object SharedVar    extends SymbolKind
      case object ConstantLit  extends SymbolKind
      case object Constant     extends SymbolKind
      case object Function     extends SymbolKind
      case object SynthFunc    extends SymbolKind
      case object Instance     extends SymbolKind
      case object CustomType   extends SymbolKind   // would use "Type" here but it's reserved.
      case object Unknown      extends SymbolKind   // bound variable, etc.

      // returns a SymbolKind indicating the Type of node in module "m" has the id "id"
      def classify(id : Identifier, m : Module) : SymbolKind = {
        val mt = m.moduleType

        if      (mt.inputMap      contains id) Input
        else if (mt.outputMap     contains id) Output
        else if (mt.sharedVarMap  contains id) SharedVar
        else if (mt.varMap        contains id) StateVar
        else if (mt.constLitMap   contains id) ConstantLit
        else if (mt.constantMap   contains id) Constant
        else if (mt.funcMap       contains id) Function
        else if (mt.synthFuncMap  contains id) SynthFunc
        else if (mt.instanceMap   contains id) Instance
        else if (m.typeDeclarationMap contains id) CustomType // TypeDecl is used already and Type is reserved word...
        else                                        Unknown
      }

      def toImportDecl(id: Identifier, origin: Module): Option[Decl] = {
        val mt = origin.moduleType
        classify(id, origin) match {
          // all "var" types need to be fed as Inputs
          case Input | Output | StateVar | SharedVar =>
            mt.typeOf(id) match {
              case Some(t) => Some(InputVarsDecl(List(id), t))
              case None => {
                System.err.println("Error: Variable " + id.toString() + " has no type.")
                None
              }
            }
          // we can just declare constants outright
          case ConstantLit => // constant literals (ex: 'const k = 5')
            Some(ConstantLitDecl(id, mt.constLitMap(id)))
          case Constant => // named constant -- don't really know how this differs from ConstantLit
            Some(ConstantsDecl(List(id), mt.constantMap(id)))
          // functions will need to be imported
          case Function => 
            Some(ModuleFunctionsImportDecl(origin.id))
          case SynthFunc =>
            Some(ModuleSynthFunctionsImportDecl(origin.id))
          // we can just copy type declarations
          case CustomType =>
            Some(TypeDecl(id, origin.typeDeclarationMap(id)))
          // TODO: If there is any type missing, add it here.
          case Instance | Unknown => None
        }
      }
    }

    // list of input var, function import, constant and type def declarations
    // should handle everything that we need from the TS module in order to run everything smoothly
    val compatVarDecls: Option[List[Decl]] = hoaData.moduleVarIdentifiers.map( ids => 
      ids.map(id => VariableIdentifier.toImportDecl(id, module)).toList
    ).flatMap{ list => 
      if(list.forall(_.isDefined)) Some(list.flatten)
      else None  
    }

    val currentState = Identifier(spec.id + "_current_state")
    val currentStateVarDecl = StateVarsDecl(List(currentState), IntegerType())
    
    
    /**
     * 2: Module Init Block 
     *   TLDR: nondeterministically select the init state from the set of possible init states
     */
    
    // init state setting
    val initStateHavoc = HavocStmt(HavocableId(currentState))
    // assume initial currentState == [initStates(0)] or == initStates(1) or ...
    // this is literally a giant conjunction of equality checks. We could use a bitvector like in the next block
    // but that's going to be messier (probably)
    val initStateAssume: Option[AssumeStmt] = hoaData.initialStates.map(states => 
      AssumeStmt(OperatorApplication(ConjunctionOp(), states.map(s => 
        OperatorApplication(EqualityOp(), List(currentState, IntLit(s)))
      ).toList), None)
    )

    val initDecl : Option[InitDecl] =
    for {            
      initStateAssume  <- initStateAssume          
    } yield    InitDecl(BlockStmt(Nil, List(initStateHavoc, initStateAssume)))// both are Decl, list type is Decl

    /**
      * 3: Module Next Block (this one is a bit confusing)
      *   TLDR: evaluate all of the conditions for edges. Keep track of the destinations we can go to using a bitvector
      *   and then nondeterministically select the next state from set of possible destinations
      */
    

    // we keep the set of valid transitions from the current state as a local bit vector, where each bit 
    // in the vector represents a state.
    // if a state's corresponding bit is 1, there exists a traverable transition from the current state to that state.
    val transitionBits = Identifier("validTransitions")
    val transitionBitsDecl = hoaData.numStates.map(n => BlockVarsDecl(List(transitionBits), BitVectorType(n)))
    val updateTransitionBits: Option[List[Statement]] = hoaData.transitionsRaw.map(tRaw => tRaw.zipWithIndex.map{ case(stateTrans, stateNum) => 
      // now we are doing per state checks -- we need one set of checks for each state
      
      // Only run state n's checks if we're on state n.
      val stateComparison = OperatorApplication(EqualityOp(), List(currentState, IntLit(stateNum)))
      val perStateTransition: List[IfElseStmt] = stateTrans.map{ case(cond, dests) => 
        // now it's per edge
        // list of statements that turn on all destinations of the edge
        val enableTransitions = dests.map(ds => AssignStmt(
            List(LhsSliceSelect(transitionBits, ConstBitVectorSlice(ds, ds))),
            List(BitVectorLit(1, 1))
        ))
        IfElseStmt(cond, BlockStmt(Nil, enableTransitions), SkipStmt())
      }
      BlockStmt(Nil, perStateTransition)
      
    })

    // Now assign the next state. We use a havoc that is limited by 2 assumes:
        // 1: that the havoc is within range of the vector
        // 2: that the bit indexed by the next state havoc is 1 (ie we can go to that state)
    val nextState = OperatorApplication(GetNextValueOp(), List(currentState))
    // assume to ensure the havoc is a valid index within the valid bits vector
    val isInRangeAssumes: Option[List[Statement]] = hoaData.numStates.map( nStates => List[Statement] (
      AssumeStmt(OperatorApplication(IntGEOp(), List(nextState, IntLit(0))), None),
      AssumeStmt(OperatorApplication(IntLTOp(), List(nextState, IntLit(nStates))), None)
    ))
    // assume to ensure that the bit indexed by the havoc var is a 1
    val isValidTransitionAssume = AssumeStmt(
      OperatorApplication( EqualityOp(), 
        List( 
          BitVectorLit(1,1), 
          OperatorApplication(VarExtractOp(VarBitVectorSlice(nextState, nextState, Some(1))), List(transitionBits))
        )
      )
    , None)
    // statement to update the next state havoc
    val updateState = List[Statement](HavocStmt(HavocableNextId(currentState)))

    val nextDecl: Option[NextDecl] =
    for {
      isInRangeAssumes <- isInRangeAssumes 
      transitionBitsDecl <- transitionBitsDecl    
      updateTransitionBits <- updateTransitionBits         
    } yield    NextDecl(BlockStmt(List(transitionBitsDecl), updateTransitionBits ++ updateState ++ isInRangeAssumes ++ List(isValidTransitionAssume)))
    
    
    /**
      * 4: Module Assembly
      */
    // Note that the module decls list is an ordered list -- ordering of these decls matters.
    val moduleDecls : Option[List[Decl]] =
    for {
      initDecl   <- initDecl                // Option[InitDecl]
      inputVarDecls <- compatVarDecls
      nextDecl <- nextDecl
    } yield inputVarDecls ++ List[Decl](currentStateVarDecl, initDecl, nextDecl)  // all are Decl, list type is Decl

    val spotModule: Option[Module] = moduleDecls.map(mDecls => Module(
      id = Identifier("LTL_Formula_" + spec.id),
      decls = mDecls,
      cmds = Nil,
      notes = Annotation.default
    ))
    println("Ofek Debug: Completed Module: " + spotModule.getOrElse(Nil).toString())
    return spotModule
    
  }


}

class LTLAutomataGenerator extends ASTRewriter(
    "LTLAutomataGenerator", new LTLAutomataGeneratorPass())
