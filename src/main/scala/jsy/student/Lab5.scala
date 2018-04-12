package jsy.student

import jsy.lab5.Lab5Like
import sun.util.resources.cldr.sr.TimeZoneNames_sr

object Lab5 extends jsy.util.JsyApplication with Lab5Like {
  import jsy.lab5.ast._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * <Anthony Tracy>
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Kyle, TAs>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  /*** Exercise with DoWith ***/

  def rename[W](env: Map[String,String], e: Expr)(fresh: String => DoWith[W,String]): DoWith[W,Expr] = {
    def ren(env: Map[String,String], e: Expr): DoWith[W,Expr] = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => doreturn(e)
      case Print(e1) =>
        ren(env, e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) =>
        ren(env, e1) map { e1p => Unary(uop, e1p) }
      case Binary(bop, e1, e2) =>
        ren(env, e1) flatMap {
          e1p => ren(env, e2) map {
            e2p => Binary(bop, e1p, e2p)
          }
        }
      case If(e1, e2, e3) =>
        ren(env, e1) flatMap {
          e1p => ren(env, e2) flatMap {
            e2p => ren(env, e3) map {
              e3p => If(e1p, e2p, e3p)
            }
          }
        }
      case Var(x) =>
        doreturn(Var(env.getOrElse(x,x)))
      case Decl(m, x, e1, e2) =>
        fresh(x) flatMap { xp =>
          ren(env, e1) flatMap {
            e1p => ren(extend(env, x, xp), e2) map {
              e2p => Decl(m, xp, e1p, e2p)
            }
          }
        }

      case Function(p, params, retty, e1) =>
        val w: DoWith[W,(Option[String], Map[String,String])] = p match {
          case None => doreturn(p, env)
          case Some(x) => fresh(x) flatMap {
            xp => doreturn(Some(xp), extend(env, x, xp))
          }
        }
        w flatMap { case (pp, envp) =>
          params.foldRight[DoWith[W,(List[(String,MTyp)],Map[String,String])]]( doreturn((Nil, envp)) ) {
            case ((x,mty), acc) => acc flatMap {
              case (l, envpp) => fresh(x) map { // FIXME
                xp => ((xp, mty) :: l, extend(envpp, x, xp))
              }
            }
          } flatMap {
            case (paramsp, envpp) => ren(envpp, e1) map {
              Function(pp, paramsp, retty, _)
            }
          }
        }
      case Call(e1, args) =>
        ren(env, e1) flatMap {
          v1 => mapWith(args)(arg => ren(env, arg)) map {
            lp => Call(v1,lp)
          }
        }
      case Obj(fields) =>
        mapWith(fields) {
          case (str, exp) => ren(env, exp) map {
            dw => (str, dw)
          }
        } map { m1 => Obj(m1) }
      case GetField(e1, f) =>
        ren(env, e1) map {
          e1p => GetField(e1p, f)
        }
      case Assign(e1, e2) =>
        ren(env, e1) flatMap {
          e1p => ren(env, e2) map {
            e2p => Assign(e1p, e2p)
          }
        }

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
    ren(env, e)
  }


  def myuniquify(e: Expr): Expr = {
    val fresh: String => DoWith[Int,String] = { _ =>
      doget flatMap {
        mem => doput(mem + 1) map {
          _ => "x" + mem.toString
        }
      }
    }
    val (_, r) = rename(empty, e)(fresh)(0)
    r
  }


  /*** Helper: mapFirst to DoWith ***/

  // List map with an operator returning a DoWith
  def mapWith[W,A,B](l: List[A])(f: A => DoWith[W,B]): DoWith[W,List[B]] = {    // Have some list of Type A's - also have a function that maps Type A -> a doWith with Types W and B
    l.foldRight[DoWith[W,List[B]]]( doreturn(Nil) ) {                           // This would however return a list of doWiths - we want a doWith[W, List[B]] though hence flatMap
      (a, acc) => f(a) flatMap {                                       // FlatMap flattens nested structs - basically python's flatten -> which would force our list of  doWith's to a doWith of a list and the W-type
        b => acc map {                                           // SO we foldright to build the list (as acc)
          bl => b :: bl                                          // We flatmap because we have a DoWith inside a DoWith so flatmap unnests them ao that we will only work on one
        }                                                        // We use map to pull the Expr out of the DoWith(mem,List(expr))
      }                                                          // then we can add expr to the list of data within the returned doWith
    }
  }

  // Map map with an operator returning a DoWith
  def mapWith[W,A,B,C,D](m: Map[A,B])(f: ((A,B)) => DoWith[W,(C,D)]): DoWith[W,Map[C,D]] = {
    m.foldRight[DoWith[W,Map[C,D]]]( doreturn( Map(): Map[C,D]) ) {
      case ((a,b), acc) => f(a,b) flatMap {
        case (c,d) => acc map {                                  // Painfully the same idea but with Maps not Lists
          macc => macc + (c -> d)                                // Needed cases to pattern match
        }                                                        // Now instead of appending to a list we have a (key,value) to update in a Map (or python dictionary)
      }
    }
  }


  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](l: List[A])(f: A => Option[DoWith[W,A]]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(Nil)                                    // Go through every element of list until we find an Element that returns Some(data) when the function is applied,
    case h :: t => f(h) match {                                         // If we get a none, recurse on the tail
      case None => mapFirstWith(t)(f) map { a => h :: a }    // Here we are makeing sure to recurse but recurse returns a doWith so we map to pull the list back out and put the head back on the front of that list
      case Some(dw) => dw map { a => a :: t}
    }
  }

  // There are better ways to deal with the combination of data structures like List, Map, and
  // DoWith, but we won't tackle that in this assignment.

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    /***** Make sure to replace the case _ => ???. */
    case(TNull, TObj(_)) => true
    case (_, _) if t1 == t2 && t1 != TNull => true
    case (TObj(f1), TObj(f2)) =>
      if (f1.size >= f2.size) {
        f2 forall {
          case (str, t2i) => f1 get str match {
            case Some(t1i) => t1i == t2i
            case None => false
          }
        }
      } else {
        f1 forall {
          case (str, t1i) => f2 get str match {
            case Some(t2i) => t2i == t1i
            case None => false
          }
        }
      }
      /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    //case (TInterface(tvar, t1p), _) => ???
    //case (_, TInterface(tvar, t2p)) => ???
      /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if fields exists { case (_, tp) => hasFunctionTyp(tp) } => true
    case _ => false
  }

  def isBindex(m: Mode, e: Expr): Boolean = (m, e) match {
    case (MConst|MName|MVar, _)   => true                   // If the mode is const, name or var, for any exr
    case (MRef, _) if isLExpr(e)  => true
    case _                        => false                  // Else we don't have a Binded expression:w
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)


    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        lookup(env, x).t
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }

        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) =>
        val t1 = typeof(env, e1)
        val t2 = typeof(env, e2)
        (t1, t2) match {
          case (TNumber, TNumber) => TNumber
          case (TString, TString) => TString
          case (_, TNumber|TString) => err(t1, e1)
          case (TNumber|TString, _) => err(t2, e2)
        }
      case Binary(Minus|Times|Div, e1, e2) =>
        val t1 = typeof(env, e1)
        val t2 = typeof(env, e2)
        (t1, t2) match {
          case (TNumber, TNumber) => TNumber
          case (_, TNumber) => err(t1, e1)
          case (TNumber, _) => err(t2, e2) //FIXME Check kmaybe for error on e2
        }
      case Binary(Eq|Ne, e1, e2) =>
        val t1 = typeof(env, e1)
        val t2 = typeof(env, e2)
        if (t1 == t2 && !hasFunctionTyp(t1)) TBool
        else err(t1, e1) // FIXME again e2
      case Binary(Lt|Le|Gt|Ge, e1, e2) =>
        val t1 = typeof(env, e1)
        val t2 = typeof(env, e2)
        (t1, t2) match {
          case (TNumber, TNumber) => TBool
          case (TString, TString) => TBool
          case (_, TNumber|TString) => err(t1, e2)
          case (TNumber|TString, _) => err(t2, e2) // FIXME again e2
        }
      case Binary(And|Or, e1, e2) =>
        val t1 = typeof(env, e1)
        val t2 = typeof(env, e2)
        (t1, t2) match {
          case (TBool, TBool) => TBool
          case (_, TBool) => err(t1, e1)
          case (TBool, _) => err(t2, e2)
        }
      case Binary(Seq, _, e2) =>
        typeof(env, e2)
      case If(e1, e2, e3) =>
        val t1 = typeof(env, e1)
        val t2 = typeof(env, e2)
        val t3 = typeof(env, e3)
        (t1, t2, t3) match {
          case (TBool, _, _) if t2 == t3 => t2
          case (_, _, _) if t2 == t3 => err(t1, e1)
          case (_, _, _) => err(t2, e2) // FIXME again error e3
        }

      case Obj(fields) =>
        TObj(fields map { case (str, exp) => (str, typeof(env, exp)) })
      case GetField(e1, f) =>
        val t1 = typeof(env, e1)
        t1 match {
          case TObj(fields) => fields.get(f) match {
            case Some(exp) => exp
            case None => err(t1, e1)
          }
          case _ => err(t1, e1)
        }

        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(m, x, e1, e2) if isBindex(m, e1) =>
        val mt1 = MTyp(m, typeof(env, e1))
        typeof(extend(env, x, mt1), e2)
      case Function(p, params, tann, e1) =>
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            extend(env, f, MTyp(MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1) {
          case (acc, (str, mtyp)) => extend(acc, str, mtyp)
        }
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, typeof(env2, e1))
          case Some(tret) =>
            val t = typeof(env2, e1)
            if (t == tret) TFunction(params, t)
            else err(t, e1)
        }

      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if params.length == args.length =>
          (params zip args).foreach {
            case ((_, MTyp(mode, typ)), arg) =>
              if (typ != typeof(env, arg) || !isBindex(mode, arg)) {
                err(typ, arg)
              }
          }
          tret
        case tgot => err(tgot, e1)
      }

        /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) =>
        val t1 = typeof(env, e1)
        lookup(env, x) match {
          case MTyp(m, xt) if (m == MVar || m == MRef) && xt == t1 => t1
          case _ => err(t1, e1)
        }
      case Assign(GetField(e1, f), e2) =>
        val t2 = typeof(env, e2)
        lookup(env, f) match {
          case MTyp(_, ftyp) if ftyp == t2 => ftyp
          case _ => err(typeof(env, e1), e1) //FIXME errpr pm e2 ?
        }
      case Assign(_, _) =>
        err(TUndefined, e)
      case Null =>
        TNull
      case Unary(Cast(t), e1) =>
        val t1 = typeof(env, e1)
        if (castOk(t1, t)) t
        else err(t1, e1)


      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 $v1 is not a value")
    require(isValue(v2), s"inequalityVal: v2 $v2 is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => if (s1.compareTo(s2) == -1) true else false
        case Le => if (s1.compareTo(s2) ==  1) false else true
        case Gt => if (s1.compareTo(s2) ==  1) true else false
        case Ge => if (s1.compareTo(s2) == -1) false else true
      }
      case (N(n1), N(n2)) => bop match {
        case Lt => n1 <  n2
        case Le => n1 <= n2
        case Gt => n1 >  n2
        case Ge => n1 >= n2
      }
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else Var(y)
      /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      /***** Cases needing adapting from Lab 4 */
      case Function(p, params, tann, e1) => p match {
        case Some(f) if x == f || params.exists { case (xi, _) => xi == x } => e
        case _ =>
          if (params.exists({ case (xi, _) => xi == x })) e
          else Function(p, params, tann, subst(e1))
      }
      /***** Cases directly from Lab 4 */
      case Call(e1, args) =>
        Call(subst(e1), args map subst)
      case Obj(fields) =>
        Obj(fields mapValues { f => subst(f) })
      case GetField(e1, f) =>
        if (x != f) GetField(subst(e1), f)
        else e
      /***** New case for Lab 5 */
      case Assign(e1, e2) =>
        Assign(subst(e1), subst(e2))
      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }

    def myrename(e: Expr): Expr = {
      val fvs = freeVars(esub)
      def fresh(x: String): String = if (fvs contains x) fresh(x + "$") else x
      rename[Unit](e)(){ x => doreturn(fresh(x)) }
    }

    subst(myrename(e))
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = (mode, e) match {
    case (MRef, _) if !isLValue(e)        => true
    case (MConst|MVar, _) if !isValue(e)  => true
    case _                                => false
  }

  def getBinding(mode: Mode, e: Expr): DoWith[Mem,Expr] = {
    require(!isRedex(mode,e), s"expression ${e} must not reducible under mode ${mode}")
    (mode,e) match {
      case (MConst,_) if isValue(e) => doreturn(e)
      case (MName,_) => doreturn(e)
      case (MVar,_) if isValue(e) => memalloc(e) map { a => Unary(Deref,a)}
      case (MRef,_) if !isValue(e) => doreturn(e)
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(n)) =>
        doreturn(N(-n))
      case Unary(Not, B(b)) =>
        doreturn(B(!b))
      case Binary(Seq, v1, e2) if isValue(v1) =>
        doreturn(e2)
      case Binary(Plus, S(s1), S(s2)) =>
        doreturn(S(s1 + s2))
      case Binary(bop @ (Plus | Minus | Times | Div), N(n1), N(n2)) => bop match {
        case Plus   => doreturn(N(n1 + n2))
        case Minus  => doreturn(N(n1 - n2))
        case Times  => doreturn(N(n1 * n2))
        case Div    => doreturn(N(n1 / n2))
      }
      case Binary(bop @ (Eq | Ne), v1, v2) if isValue(v1) && isValue(v2) => bop match {
        case Eq => doreturn(B(v1 == v2))
        case Ne => doreturn(B(v1 != v2))
      }
      case Binary(bop @ (Lt | Le | Gt | Ge), v1 @ (N(_) | S(_)), v2 @ (N(_) | S(_))) =>
        doreturn(B(inequalityVal(bop, v1, v2)))
      case Binary(And, B(b), e2) =>
        if (b) doreturn(e2)
        else doreturn(B(false))
      case Binary(Or, B(b), e2) =>
        if (b) doreturn(B(true))
        else doreturn(e2)
      case If(B(b), e2, e3) =>
        if (b) doreturn(e2)
        else doreturn(e3)
        /***** More cases here */
        /***** Cases needing adapting from Lab 4. */
      case Obj(fields) if fields forall { case (_, vi) => isValue(vi) } =>
        memalloc(e)
      case GetField(a @ A(_), f) =>
        doget flatMap {
          m => m.get(a) match {
            case Some(Obj(fields)) => fields.get(f) match {
              case Some(v) => doreturn(v)
              case None => throw StuckError(e)
            }
            case None => throw NullDereferenceError(e)
          }
        }
      case GetField(Null, _) =>
        throw NullDereferenceError(e)
      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        getBinding(MConst, v1) map { e1p => substitute(e2, e1p, x) }
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        getBinding(MVar, v1) map { e1p => substitute(e2, e1p, x) }

        /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) =>
        doget map { m => m(a) }
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m => m + (a -> v) } map { _ => v }
      case Assign(GetField(a @ A(_), f), vp) if isValue(vp) =>
        domodify[Mem] {
          m => m.get(a) match {
            case Some(Obj(fields)) => m + (a -> Obj(fields + (f -> vp)))
            case None => throw NullDereferenceError(e)
          }
        } map { _ => vp }
      case Assign(GetField(Null, _), _) =>
        throw NullDereferenceError(e)
      // Function(p: Option[String], params: List[(String,MTyp)], tann: Option[Typ], e1: Expr)
      // args: List[Expr]
      case Call(v @ Function(p, params, _, e), args) =>
        val pazip = params zip args
        if (pazip.forall { case ((_, MTyp(m, _)), ep) => !isRedex(m, ep) }) {
          val dwep = pazip.foldRight( doreturn(e) : DoWith[Mem,Expr] )  {
            case (((xi, MTyp(mi, _)), ei), dwacc) => getBinding(mi,ei) flatMap {
              e1p => dwacc map {
                ebod => substitute(ebod, e1p, xi)
              }
            }
          }
          p match {
            case None => dwep
            case Some(x) => dwep map { ebod => substitute(ebod, v, x) }
          }
        }
        else {
          val dwpazipp = mapFirstWith(pazip) {
            case (pi @ (_, MTyp(m, _)), ei) if isRedex(m, ei) => Some(step(ei) map { ap => (pi, ap) })
            case _ => None
          }
          dwpazipp map {
            arg => Call(v, arg map { case ((_,_), exp) => exp})
          }
        }
      case Unary(Cast(t), e1) => (t, e1) match {
        case (TObj(fields), a @ A(_)) => doget map {
          m => m get a match {
            case Some(Obj(fp)) =>
              if (fields forall { case (fi,_) => fp contains fi }) a
              else throw DynamicTypeError(e)
            case _ => throw DynamicTypeError(e)
          }
        }
        case (_, v) if v != Null => doreturn(v)
        case (TObj(_), Null) => doreturn(Null)
      }


      /* Base Cases: Error Rules */
        /***** Replace the following case with a case to throw NullDeferenceError.  */
      //case _ => throw NullDeferenceError(e)

      /* Inductive Cases: Search Rules */
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) =>
        step(e1) map { e1p => Unary(uop, e1p) }
      case Binary(bop, v1, e2) if isValue(v1) =>
        step(e2) map { e2p => Binary(bop, v1, e2p) }
      case Binary(bop, e1, e2) =>
        step(e1) map { e1p => Binary(bop, e1p, e2) }
      case If(e1, e2, e3) =>
        step(e1) map { e1p => If(e1p, e2, e3) }
        /***** Cases needing adapting from Lab 4 */
      case GetField(e1, f) =>
        step(e1) map { e1p => GetField(e1p, f) }
      case Obj(fields) =>
        fields find { case (_, exp)  => !isValue(exp) } match {
          case Some((fi, ei)) => step(ei) map { eip =>
            Obj(fields + (fi -> eip))
          }
          case None => throw StuckError(e)
        }
      case Decl(mode, x, e1, e2) if isRedex(mode, e1) =>
        step(e1) map { e1p => Decl(mode, x, e1p, e2) }
      case Call(e1, args) =>
        step(e1) map { e1p => Call(e1p, args) }

        /***** New cases for Lab 5.  */    // So enforcing left to right evaluation:
      case Assign(e1, e2) if !isLValue(e1) =>
        step(e1) map {
          e1p => Assign(e1p, e2)
        }
      case Assign(e1, e2) =>
        step(e2) map {
          e2p => Assign(e1, e2p)
        }

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def lower(e: Expr): Expr =
    /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

