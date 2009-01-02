#include "util/thread.h"
#include <iostream>

CompletionCounter cc;

void *foo(void* info){
  for(int i=0;i<10;i++){
    sleep(1);
    cc.complete();
    printf("test%i\n", i);
    fflush(stdout);
  }
  return NULL;
}

int main(){
  cc = CompletionCounter(3);
  pthread_t thread;

  pthread_create(&thread, NULL, foo, NULL);
  printf("test\n");
  fflush(stdout);
  cc.wait();
  pthread_join(thread, NULL);
  
  return 0;
}
