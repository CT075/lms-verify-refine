#include <limits.h>
/*@
requires (x0<5);
assigns \nothing;
ensures (\result<10);
*/
int foo(int  x0) {
  /*@assert (5<10);*/
  return x0;
}
