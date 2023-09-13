#include <limits.h>
/*@
assigns \nothing;
ensures (\result<10);
*/
int foo(int  x0) {
  int x3 = x0 < 10;
  int x6;
  if (x3) {
    /*@assert x3;*/
    x6 = x0;
  } else {
    x6 = 9;
  }
  /*@assert (((x3) ? (x0) : (9))<10);*/
  return x6;
}
