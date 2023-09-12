package lms.verify

class RefineTestBasic extends TestSuite {
  val under = "refine"

  trait Refines extends Dsl with DataOps {
    sealed trait Proof[P] {
      def emit(): Rep[Unit]
    }

    def unsafeAssert[P](cond: Rep[Boolean]): Proof[P] = new Proof[P] {
      def emit() = _assert(cond)
    }

    trait Predicate[A] {
      def verify(x: Rep[A]): Rep[Boolean]
    }

    case class TRUE[A]() extends Predicate[A] {
      def verify(x: Rep[A]): Rep[Boolean] = {
        unit(true)
      }
    }

    def _true[A](): Proof[TRUE[A]] = new Proof[TRUE[A]] {
      def emit() = {}
    }

    case class Refined[A: Manifest, P <: Predicate[A]](x: Rep[A], proof: Proof[P]) {
      def unwrap(): Rep[A] = {
        proof.emit()
        x
      }
    }

    def check[A: Manifest, P <: Predicate[A], B](
      x: Rep[A],
      _then: Refined[A, P] => Rep[B],
      _else: => Rep[B]
    )(implicit ev: Typ[B], pred: P) : Rep[B] = {
      val cond: Rep[Boolean] = pred.verify(x)
      if (cond) _then(Refined(x, unsafeAssert(cond))) else _else
    }

    // It'd be nice to do this implicitly
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
        requireAndEnsure[Int, Int, TRUE[Int], LessThan10](
          max9
        )_
      )
    }

    check("1", (new Ex1 with Impl).code)
  }
}
