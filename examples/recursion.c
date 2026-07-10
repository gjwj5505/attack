int f(int x){
    int ret;
    if(x == 0) return 0;
    ret = f(x - 1);
    return ret;
}

int main(){
    int result;
    result = f(2);
    return result;
}