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

    def leftpad[A:Iso:Eq](c: A, src: Vec[A], dst: Vec[A]): Rep[Unit] = {
      dst.a.reflectMutableInput
      val n = dst.length
      val l = src.length
      if (n > l) {
        val p = n - l;
        for (i <- 0 until l) {
          loop_assigns(list_new(i::dst.a.within(p until n)))
          //loop_invariant(dst.slice(p,p+i-1).equals(src.slice(0,i-1)))
          dst.a(p+i) = src(i)
        }
        for (i <- 0 until p) {
          loop_assigns(list_new(i::dst.a.within(0 until p)))
          loop_invariant(dst.slice(0,i-1).forall{x => x deep_equal c})
          dst.a(p-1-i) = c;
        }
      }

      unit(())
    }

    def mk[A:Iso:Eq] =
      toplevel("leftpad", {(c: A, src:Vec[A], dst:Vec[A]) => leftpad(c,src,dst)})
  }

  test("1") {
    trait LP1 extends LeftPadder {
      implicit def eq = equality[Rep[Int]](_ == _)
      mk[Rep[Int]]
    }
    //check("1", (new LP1 with Impl).code)
  }
}
