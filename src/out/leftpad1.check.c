#include <limits.h>
/*@ predicate eq_Int(int  x0, int  x1) = (x0==x1);*/
/*@
assigns \nothing;
ensures \result <==> eq_Int(x0, x1);
*/
int eq_Int(int  x0, int  x1) {
  int x3 = x0 == x1;
  return x3;
}
/*@ predicate inv_vec_Int(int  * x4, integer  x5) = ((x5==0) || ((x5>0) &&
\valid(x4+(0..x5-1))));*/
/*@
requires ((inv_vec_Int(x20,x21) &&
inv_vec_Int(x22,x23)) &&
(x23>=x21));
ensures ((inv_vec_Int(x20,x21) &&
inv_vec_Int(x22,x23)) &&
(\forall int  x88; ((((0<=x88) &&
(x88<(x23-x21))) ==> eq_Int(x22[x88],x19)) &&
((((x23-x21)<=x88) &&
(x88<x23)) ==> eq_Int(x20[(x88-(x23-x21))],x22[x88])))));
*/
void leftpad(int  x19, int  * x20, int  x21, int  * x22, int  x23) {
  int x26 = x23 > x21;
  if (x26) {
    int x27 = x21 + 1;
    int x25 = x23 - x21;
    /*@
    loop invariant 0<=x29<=x27;
    loop invariant (((((x25+x29)-1)-x25)==(x29-1)) &&
    (\forall int  x39; (((0<=x39) &&
    (x39<(((x25+x29)-1)-x25))) ==> eq_Int(x22[(x25+x39)],x20[x39]))));
    loop assigns x29, x22[(x25..x23-1)];
    loop variant x27-x29;
    */
    for(int x29=0; x29 < x27; x29++) {
      int x51 = x20[x29];
      x22[x34] = x51;
    }
    int x70 = x25 - 1;
    /*@
    loop invariant 0<=x56<=x25;
    loop invariant (\forall int  x61; (((0<=x61) &&
    (x61<(x56-1))) ==> eq_Int(x22[x61],x19)));
    loop assigns x56, x22[(0..x25-1)];
    loop variant x25-x56;
    */
    for(int x56=0; x56 < x25; x56++) {
      int x71 = x70 - x56;
      x22[x71] = x19;
    }
  } else {
  }
}
