package lms.verify

class RefineTestBasic extends TestSuite {
  val under = "refine"

  trait Refines extends Dsl with DataOps {
    trait Prop[A] {
      def reify(x: Rep[A]): Rep[Boolean]
    }

    trait Proof[A, P <: Prop[A]] {}

    case class Refined[A, P <: Prop[A]](x: Rep[A], proof: Proof[A,P])

    def unsafeProve[A, P <: Prop[A]]: Proof[A,P] = new Proof[A,P] {}

    def requires_[A, P <: Prop[A]](x: Rep[A], p: P) = {
      requires(p.reify(x))
      Refined(x, unsafeProve[A,P])
    }

    def contractsOfRefines[A:Typ, PA <: Prop[A], B:Typ, PB <: Prop[B]]
      (f: Refined[A, PA] => Refined[B, PB])
      (implicit pa: PA, pb: PB): Rep[A] => Rep[B] = { x =>
        val rx = requires_[A, PA](x, pa)
        val y = f(rx).x
        ensures{result: Rep[B] => pb.reify(result)}
        y
    }
  }

  test("1") {
    trait Ex1 extends Refines {
      implicit object P extends Prop[Int] {
        def reify(x: Rep[Int]) = x < 10
      }

      toplevel("id",
        // TODO: make this implicit
        contractsOfRefines[Int, P.type, Int, P.type]{ (x: Refined[Int, P.type]) => x }
      )
    }

    check("1", (new Ex1 with Impl).code)
  }
}
