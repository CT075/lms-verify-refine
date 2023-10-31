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
(\forall int  x76; ((((0<=x76) &&
(x76<(x23-x21))) ==> eq_Int(x22[x76],x19)) &&
((((x23-x21)<=x76) &&
(x76<x23)) ==> eq_Int(x22[x76],x20[(x76-(x23-x21))])))));
*/
void leftpad(int  x19, int  * x20, int  x21, int  * x22, int  x23) {
  int x25 = x23 - x21;
  /*@
  loop invariant 0<=x27<=x21;
  loop invariant (\forall int  x28; (((0<=x28) &&
  (x28<x27)) ==> eq_Int(x22[(x28+x25)],x20[x28])));
  loop assigns x27, x22[(x25..x23-1)];
  loop variant x21-x27;
  */
  for(int x27=0; x27 < x21; x27++) {
    int x43 = x27 + x25;
    int x44 = x20[x27];
    x22[x43] = x44;
  }
  /*@
  loop invariant 0<=x49<=x25;
  loop invariant (\forall int  x50; (((0<=x50) &&
  (x50<x49)) ==> eq_Int(x22[x50],x19)));
  loop assigns x49, x22[(0..x25-1)];
  loop variant x25-x49;
  */
  for(int x49=0; x49 < x25; x49++) {
    x22[x49] = x19;
  }
}
