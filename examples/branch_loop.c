int main() {
  int a = 6;
  int b = 4;
  int acc = 0;
  while (a > 0) {
    if ((a % 2) == 0) {
      acc = acc + b;
    } else {
      acc = acc - 1;
    }
    a = a - 1;
    b = b + 1;
  }
  return acc;
}
