# l

Simple array language, right now the idea is to provide an implementation
of k6 http://kparc.com/k.txt.

Little of the language is actually implemented, just the parser and a couple of functions.
The parser is written following the implementation shown in the book "an implementation of j".

## Run
``` gcc l.c -o l && ./l ```
Try:
``` 1;2+2;3+4-1;!5;3+!5 ```

## Todo
- [ ] Error system
- [ ] Implement verbs
- [ ] Implement adverbs
- [ ] Improve logging
- [ ] Buddy allocator
- [ ] Tons of other stuff
