  int f(int x);
  int g(int x);

  int f(int x) {
      int ret;
      ret = g(x);
      return ret;
  }

  int g(int x) {
      if (x == 0) return 0;
      return f(x - 1);
  }

  int main() {
      int result;
      result = f(2);
      return result;
  }