int g = 3;

int inc(int x) {
  int y;

  y = x + 1;
  return y;
}

int main(void) {
  int a[2];
  int *p;
  int r;

  a[0] = g;
  p = &a[0];
  r = inc(*p);
  return 0;
}
