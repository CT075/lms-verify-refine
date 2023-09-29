package lms.verify

class LoopTest extends TestSuite {
  val under = "refine"

  trait Refines extends Dsl with DataOps {
    trait Prop {
      def emit(): Rep[Boolean]
    }

    sealed trait Proof[P] {
      def emit(): Rep[Unit]
    }

    sealed trait &&&[P, Q]
    sealed trait |||[P, Q]
    sealed trait -->[P, Q]

    // `unsafeAssert` does exactly what it says on the tin, and asserts that
    // a given `Rep[Bool]` is true. It is "unsafe" in that there is no
    // guarantee that this assertion will be accepted by the underlying prover.
    case class unsafeAssert[P](cond: Rep[Boolean]) extends Proof[P] {
      def emit() = _assert(cond)
    }

    // Basic propositional logic combinators...

    case class andIntro[P, Q](p: Proof[P], q: Proof[Q]) extends Proof[&&&[P, Q]] {
      def emit() = {
        p.emit()
        q.emit()
      }
    }

    case class orIntro1[P, Q](p: Proof[P]) extends Proof[|||[P, Q]] {
      def emit() = p.emit()
    }

    case class orIntro2[P, Q](q: Proof[Q]) extends Proof[|||[P, Q]] {
      def emit() = q.emit()
    }

    case class andElim1[P, Q](pq: Proof[&&&[P, Q]]) extends Proof[P] {
      def emit() =
        pq match {
          case andIntro(p, q) => p.emit()
          // what to do if we see `unsafeAssert`?
          case _ => unit(())
        }
    }

    case class andElim2[P, Q](pq: Proof[&&&[P, Q]]) extends Proof[Q] {
      def emit() =
        pq match {
          case andIntro(p, q) => q.emit()
          case _ => unit(())
        }
    }

    // CR cam: how to do `orElim`?

    // A `Predicate[A]` is a proposition taking one free variable of type `A`.
    trait Predicate[A] {
      def verify(x: Rep[A]): Rep[Boolean]
    }

    case class TRUE[A]() extends Predicate[A] {
      def verify(x: Rep[A]): Rep[Boolean] = {
        unit(true)
      }
    }

    // Proofs of `true` don't need to be emitted.
    def _true[A](): Proof[TRUE[A]] = new Proof[TRUE[A]] {
      def emit() = {}
    }

    // A `Refined[A,P]` holds `x: Rep[A]` and a proof that `x` satisfies `P`.
    // It cannot be used directly as a `Rep`, but must instead be `unwrap`ped
    // to ensure that the right proofs get emitted in the generated code.
    //
    // CR cam: We don't need to acually reference `x` in `proof`, which means
    // we can build a `Proof[P]` for a different variable, then refine `x` with
    // it. There's probably a way to resolve this by making `Refined` contain a
    // path-dependent type.
    case class Refined[A: Manifest, P <: Predicate[A]](x: Rep[A], proof: Proof[P]) {
      def unwrap(): Rep[A] = {
        proof.emit()
        x
      }
    }

    def weaken[A: Manifest, P <: Predicate[A], Q <: Predicate[A]](
      x: Refined[A, P],
      f: Proof[P] => Proof[Q]
    ): Refined[A, Q] = {
      x match {
        case Refined(x, p) => Refined(x, f(p))
      }
    }

    // This is a dependent `if` statement, in which we check a condition and
    // use the proof in the `_then` branch.
    //
    // CR cam: The output here is forced to be `Rep[B]` rather than something
    // more general (for example, disallowing `Refined[B, _]`) because I
    // couldn't figure out how else to make the virtualizer accept `if (cond)`.
    def check[A: Manifest, P <: Predicate[A], B](
      x: Rep[A],
      _then: Refined[A, P] => Rep[B],
      _else: => Rep[B]
    )(implicit ev: Typ[B], pred: P) : Rep[B] = {
      val cond: Rep[Boolean] = pred.verify(x)
      if (cond) _then(Refined(x, unsafeAssert(cond))) else _else
    }

    // A helper function transforming refinements on the input/output
    // parameters into a traditional `Rep=>Rep` function with requires and
    // ensures.
    //
    // CR cam: It'd be nice to not have to do this.
    def requireAndEnsure[
      A: Manifest,
      B: Manifest,
      Requires <: Predicate[A],
      Ensures <: Predicate[B]
    ](
      f: Refined[A, Requires] => Refined[B, Ensures]
    )(x: Rep[A])
    (implicit precond: Requires, postcond: Ensures, evB: Typ[B]): Rep[B] = {
      requires(precond.verify(x))
      ensures(postcond.verify)

      f(Refined(x, unsafeAssert(precond.verify(x)))).unwrap()
    }
  }

  test("1") {
    trait Ex1 extends Refines {
      case class LessThan10() extends Predicate[Int] {
        def verify(x: Rep[Int]) = x < 10
      }

      implicit val lt10 = LessThan10()
      implicit val theTrue = TRUE[Int]()

      def max9(x: Refined[Int, TRUE[Int]]): Refined[Int, LessThan10] = {
        val result =
          check[Int, LessThan10, Int](
            x.unwrap(),
            (t: Refined[Int, LessThan10]) => t.unwrap(),
            unit(9)
          )

        Refined(
          result,
          unsafeAssert(result < 10)
        )
      }

      toplevel("foo",
        requireAndEnsure[Int, Int, TRUE[Int], LessThan10](max9)_
      )
    }

    check("1", (new Ex1 with Impl).code)
  }
}
