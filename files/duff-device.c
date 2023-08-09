/* An example of coroutines in C via the Duff Device 
 *
 * Programmer: Mayer Goldberg, 2011
 */

#include <stdio.h>
#include <string.h>

#define crBegin static int state=0; switch(state) { case 0:
#define crReturn(x) do {state=__LINE__; return (x); case __LINE__:;} while (0)
#define crFinish } 

char *function() {
  static char buffer[512];
  static int i, j;
  crBegin;
  for (i = 0; i < 5; ++i) {
    for (j = 0; j < 5; ++j) {
      sprintf(buffer, "%d * %d = %d", i, j, i * j);
      crReturn(buffer);
    }
    sprintf(buffer, "end of row %d", i);
    crReturn(buffer);
  }
  crFinish;
  return "end";
}

int main() {
  int i;

  for (i = 0; i < 35; ++i) {
    printf("%s\n", function());
  }

  return 0;
}
