#define x y

int main() {
  int x = 3;

  while (x > 0) {
    x = x - 1;
    x = x / 0;
  }

  return x;
}
