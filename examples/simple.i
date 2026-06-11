# 0 "simple.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "simple.c"


int main() {
  int y = 3;

  while (y > 0) {
    y = y - 1;
    y = y / 0;
  }

  return y;
}
