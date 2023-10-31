package lms.verify

class LeftPadTests extends TestSuite {
  val under = "leftpad"

  trait LeftPadder extends Dsl with DataOps { dsl =>
    def key[T:Iso] = implicitly[Iso[T]].id
    class Vec[T:Iso](val a: Pointer[T], val n: Rep[Int]) {
      def apply(i: Rep[Int]) = a(i)
      def valid = n==0 || (n>0 && a.valid(0 until n))
      def length = n
    }
    implicit def vecIso[T:Iso](implicit ev: Inv[Vec[T]]) = isodata[Vec[T],(Pointer[T],Rep[Int])](
      "vec_" + key[T],
      {x: Vec[T] => (x.a, x.n)},
      {x: (Pointer[T],Rep[Int]) => new Vec(x._1, x._2)}
    )
    implicit def vecInv[T:Inv] = invariant[Vec[T]] { x =>
      x.valid && ((0 until x.n) forall {i => x(i).check})
    }
    implicit def vecEq[T:Eq:Iso] = equality[Vec[T]] { (x, y) =>
      x.n == y.n && ((0 until x.n) forall {i => x(i) deep_equal y(i)})
    }
    def infix_separated[T:Iso](v: Vec[T]): Rep[Boolean] = {
      val (x, n) = (v.a, v.n)
      val pn: Int = x.p.size
      and_list((for (i <- 0 until pn: Range; j <- (i+1) until pn: Range) yield {
        val (a01,(m01,t01)) = x.pmt(i)
        val (a02,(m02,t02)) = x.pmt(j)
        implicit val t1 = t01.asInstanceOf[Typ[m01.T]]
        val a1 = a01.asInstanceOf[Rep[Array[m01.T]]]
        implicit val t2 = t02.asInstanceOf[Typ[m02.T]]
        val a2 = a02.asInstanceOf[Rep[Array[m02.T]]]
        forall{i1: Rep[Int] => forall{i2: Rep[Int] =>
          (0 <= i1 && i1 < n && 0 <= i2 && i2 < n) ==>
          separated(a1, i1, a2, i2)
        }}}).toList)
    }
    case class VecRange[T:Eq:Iso](v: Vec[T], start: Rep[Int], end: Rep[Int]) {
      def forall(p: T => Rep[Boolean]) = dsl.forall{i: Rep[Int] =>
        (start <= i && i < end) ==> p(v(i))
      }
      def length = end-start
      def apply(i: Rep[Int]) = v(start+i)
      def equals(other: VecRange[T]): Rep[Boolean] = {
        length == other.length &&
        dsl.forall{i: Rep[Int] =>
          ((0 <= i && i < length) ==> (v(start+i) deep_equal other(i)))
        }
      }
    }
    def infix_slice[T:Eq:Iso](v: Vec[T], i: Rep[Int], j: Rep[Int]) = VecRange(v, i, j)

    def leftpadManual[A:Iso:Eq](c: A, src: Vec[A], dst: Vec[A]): Rep[Unit] = {
      dst.a.reflectMutableInput
      val n = dst.length
      val l = src.length
      val p = n - l
      requires(n >= l)
      ensures((result: Rep[Unit]) =>
        dsl.forall{i: Rep[Int] => {
          ((0 <= i && i < p) ==> (dst(i) deep_equal c)) &&
          ((p <= i && i < n) ==> (dst(i) deep_equal src(i-p)))
        }})
      dst.a.reflectMutableInput

      for (i <- 0 until l) {
        loop_assigns(list_new(i::dst.a.within(p until n)))
        loop_invariant(dsl.forall{x: Rep[Int] => {
          ((0 <= x && x < i) ==> (dst(x+p) deep_equal src(x)))
        }})

        dst.a(i+p) = src(i)
      }
      for (i <- 0 until p) {
        loop_assigns(list_new(i::dst.a.within(0 until p)))
        loop_invariant(dst.slice(0,i).forall{x => x deep_equal c})
        dst.a(i) = c;
      }

      unit(())
    }

    trait Proof {
      def reify(): Rep[Boolean]
    }

    def liftMutableAssign[A:Eq](cell: A, vl: A): Proof = new Proof {
      def reify() = cell deep_equal vl
    }

    // TODO: return P as well
    def forAll[P <: Proof](r: Rep[Range], inv: Rep[Int] => P, body: (Rep[Int], P) => P) = {
      for (x <- r) {
        val invW = inv(x)
        loop_invariant(invW.reify())
        body(x, invW)
        unit(())
      }
    }

    def leftpad[A:Iso:Eq](c: A, src: Vec[A], dst: Vec[A]): Rep[Unit] = {
      dst.a.reflectMutableInput
      val n = dst.length
      val l = src.length
      val p = n - l
      requires(n >= l)
      ensures((result: Rep[Unit]) =>
        dsl.forall{i: Rep[Int] => {
          ((0 <= i && i < p) ==> (dst(i) deep_equal c)) &&
          ((p <= i && i < n) ==> (dst(i) deep_equal src(i-p)))
        }})
      dst.a.reflectMutableInput

      case class CopyInvariant(val i: Rep[Int]) extends Proof {
        def reify() = dsl.forall{x: Rep[Int] => {
          ((0 <= x && x < i) ==> (dst(x+p) deep_equal src(x)))
        }}
      }

      forAll[CopyInvariant](0 until l, CopyInvariant.apply, {(i: Rep[Int], pf: CopyInvariant) =>
        loop_assigns(list_new(i::dst.a.within(p until n)))
        dst.a(i+p) = src(i)
        // TODO: join with the lifted assign above
        pf
      })

      case class PadInvariant(val i: Rep[Int]) extends Proof {
        def reify() = dsl.forall{x: Rep[Int] => {
          ((0 <= x && x < i) ==> (dst(x) deep_equal c))
        }}
      }

      forAll[PadInvariant](0 until p, PadInvariant.apply, {(i: Rep[Int], pf: PadInvariant) =>
        loop_assigns(list_new(i::dst.a.within(0 until p)))
        dst.a(i) = c
        pf
      })

      unit(())
    }

    def mkManual[A:Iso:Eq] =
      toplevel("leftpadManual", {(c: A, src:Vec[A], dst:Vec[A]) => leftpadManual(c,src,dst)})

    def mk[A:Iso:Eq] =
      toplevel("leftpad", {(c: A, src:Vec[A], dst:Vec[A]) => leftpad(c,src,dst)})
  }

  test("manual") {
    trait LPManual extends LeftPadder {
      implicit def eq = equality[Rep[Int]](_ == _)
      mkManual[Rep[Int]]
    }
    check("manual", (new LPManual with Impl).code)
  }

  test("witnessed") {
    trait LPWitness extends LeftPadder {
      implicit def eq = equality[Rep[Int]](_ == _)
      mk[Rep[Int]]
    }
    check("witnessed", (new LPWitness with Impl).code)
  }
}