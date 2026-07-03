int f(int x){
    int f1;
    int f2;
    int ret;
    if(x <= 2){
        return 1;
    }
    else{
        f1 = f(x - 1);
        f2 = f(x - 2);
        ret = f1 + f2;
        return ret;
    }
}

int main(){
    int ret;
    ret = f(3);
    return ret;
}