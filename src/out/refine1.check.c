#include <limits.h>
/*@
requires (x0<10);
assigns \nothing;
ensures (\result<10);
*/
int id(int  x0) {
  return x0;
}
