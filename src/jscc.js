kernel.add('jscc', function() {
  return function(grammar, start, tokens) {
    // TODO: check for misplaced epsilons, missing start symbol, collision with augmented start symbol, etc.
    // TODO: raise errors when terminals are prefixes of one another
    
    if (!tokens) tokens = {};
    grammar[start+"'"] = [[[start], function(e) { return e; }]];
    start = start+"'";
    
    var terminals = {}, nonterminals = Object.keys(grammar),
        firsts = {}, follows = {}, items = [],
        done;

    // utility functions
    var production = function(i) {
      return i[0]+' → '+i[1].map(function(j, k) {
        return k != i[2] ? k ? ' '+j : j : '•'+j;
      }).join('')+(i[2] == i[1].length ? '•' : '');
    };
    
    var eachProduction = function(fn) {
      nonterminals.forEach(function(n) {
        grammar[n].forEach(function(p) { fn(n, p[0]); });
      });
    };
    
    eachProduction(function(n, production) {
      production.forEach(function(symbol) {
        if (!grammar.hasOwnProperty(symbol))
          terminals[symbol] = 1;
      });
    });
    terminals = Object.keys(terminals);
    
    nonterminals.forEach(function(n) {
      firsts[n] = {};
      follows[n] = {};
    });
    
    // compute first sets
    do {
      done = true;
      eachProduction(function(n, production) {
        (function getFirst(i) {
          if (!production.length) return [''];
          var first = production[i];
          if (!grammar.hasOwnProperty(first)) return [first];
          if (i == production.length-1) return Object.keys(firsts[first]);
          var noepsilon = Object.keys(firsts[first]).filter(function(t) { return t != ''; });
          return firsts[first].hasOwnProperty('') ? noepsilon.concat(getFirst(i+1)) : noepsilon;
        })(0).forEach(function(first) {
          if (firsts[n].hasOwnProperty(first)) return;
          firsts[n][first] = 1;
          done = false;
        });
      });
    } while (!done);
    
    // compute follow sets
    follows[start][''] = 1;
    do {
      done = true;
      eachProduction(function(n, production) {
        var current, next, epsilonFollow = true;
        for (var i = production.length-1; i >= 0; i--) {
          if (!grammar.hasOwnProperty(current = production[i])) continue;
          if (next = production[i+1]) {
            if (!grammar.hasOwnProperty(next)) {
              epsilonFollow = false;
              if (follows[current].hasOwnProperty(next)) continue;
              follows[current][next] = 1;
              done = false;
            } else {
              epsilonFollow = epsilonFollow && firsts[next].hasOwnProperty('');
              Object.keys(firsts[next]).forEach(function(follow) {
                if (follow == '' || follows[current].hasOwnProperty(follow)) return;
                follows[current][follow] = 1;
                done = false;
              });
            }
          }
          if (epsilonFollow) {
            Object.keys(follows[n]).forEach(function(follow) {
              if (follows[current].hasOwnProperty(follow)) return;
              follows[current][follow] = 1;
              done = false;
            });
          }
        }
      });
    } while (!done);
    
    //nonterminals.forEach(function(n) { console.log('first', n, Object.keys(firsts[n])); });
    //nonterminals.forEach(function(n) { console.log('follow', n, Object.keys(follows[n])); });
    
    // compute states
    
    // adds any nonkernel productions to complete closure,
    // as well as all transition symbols
    var close = function(state) {
      var transitions = {}, done;
      state.forEach(function(i) {
        if (i = i[1][i[2]]) transitions[i] = 0;
      });
      do {
        done = true;
        Object.keys(transitions).forEach(function(symbol) {
          if (!grammar.hasOwnProperty(symbol)) return;
          grammar[symbol].forEach(function(production) {
            if (!state.some(function(i) { return i[1] == production[0] && !i[2]; })) {
              var next = production[0][0];
              if (!next) return;
              state.push([symbol, production[0], 0, production[1]]);
              transitions[next] = 0;
              if (grammar.hasOwnProperty(next)) done = false;
            }
          });
        });
      } while (!done);
      return {state: state, transitions: transitions, reductions: {}};
    };
    
    items.push(close([[start, grammar[start][0][0], 0, grammar[start][0][1]]]));
    
    do {
      done = true;
      items.forEach(function(item) {
        Object.keys(item.transitions).forEach(function(symbol) {
          // find all productions in item with symbol as
          // their next symbol and advance index; these
          // become kernel of another item, which we add
          // to items if it doesn't already exist
          var it = [];
          item.state.forEach(function(i) {
            var production = i[1],
                index = i[2],
                next = production[index];
            if (next && next == symbol)
              it.push([i[0], production, index+1, i[3]]);
          });
          
          //console.log('item candidate\n'+it.map(production).join('\n'));
          
          if (!items.some(function(item) {
            var compared = 0;
            return !item.state.some(function(i) {
              if (!i[2] && i[1] != grammar[start][0][0]) return;
              compared++;
              return !it.some(function(j) {
                return i[1] == j[1] && i[2] == j[2];
              });// && (console.log(production(i)+' not in new item') || true) || console.log(production(i)+' found in new item');
            }) && compared == it.length && (it = item);
          })) {
            items.push(it = close(it));
            done = false;
          }
          item.transitions[symbol] = it;
        });
      });
    } while (!done);
    
    /*console.log(items.length+' items:\n\n'+items.map(function(item) {
      return item.state.map(production).join('\n');
    }).join('\n\n'));*/
    
    // detect shift-reduce, reduce-reduce conflicts
    items.forEach(function(item) {
      item.state.forEach(function(i) {
        var next = i[1][i[2]];
        if (next) {
          if (item.reductions.hasOwnProperty(next)) throw 'shift-reduce conflict between productions on input "'+next+'"\n  '+production(i)+' (shift)\n  '+production(item.transitions[next])+' (reduce)';
        } else {
          Object.keys(follows[i[0]]).forEach(function(next) {
            if (item.transitions.hasOwnProperty(next)) throw 'shift-reduce conflict between productions on input "'+next+'"\n  '+production(item.transitions[next])+' (shift)\n  '+production(i)+' (reduce)';
            if (item.reductions.hasOwnProperty(next)) throw 'reduce-reduce conflict between productions on input "'+next+'"\n  '+production(item.reductions[next])+'\n  '+production(i);
            item.reductions[next] = i;
          });
        }
      });
    });
    
    return function(string) {
      var token, match, ignore = tokens[''], substring = string, tree = [], stack = [], state = items[0], i = 0;
      
      while (state) {
        //console.log('now at:\n'+state.state.map(production).join('\n'));
        
        token = undefined;
        
        if (ignore && (match = ignore.exec(substring))) {
          substring = substring.substr(match[0].length);
          i += match[0].length;
          continue;
        }
        
        (function(process) {
          Object.keys(state.transitions).forEach(process(false));
          Object.keys(state.reductions).forEach(process(true));
        })(function(reduce) {
          return function(symbol) {
            //console.log('checking symbol '+symbol);
            if (symbol && tokens.hasOwnProperty(symbol)) {
              // TODO: anchor each token regex to the beginning of substring
              // (or eliminate substring if possible to match starting at index i of program)
              if ((match = tokens[symbol].exec(substring)) && (!token || match[0].length > token.value.length))
                token = {symbol: symbol, value: match[0], reduce: reduce};
            } else if (substring.substr(0, symbol.length) == symbol && (!token || symbol.length > token.value.length) && (symbol || i == string.length)) {
              token = {symbol: symbol, value: symbol, reduce: reduce};
            }
          };
        });
        
        if (!token) {
          var before = string.substr(0, i),
              newlines = before.match(/\n/g),
              lastNewline = before.lastIndexOf('\n') + 1;
          throw {
            message: 'Unidentified token',
            index: i,
            line: string.substring(lastNewline, (string+'\n').indexOf('\n', lastNewline)),
            row: newlines ? newlines.length+1 : 1,
            column: i - lastNewline
          };
        }
        
        if (token.reduce) {
          var values = [],
              reduction = state.reductions[token.symbol];
          reduction[1].forEach(function() {
            state = stack.pop();
            values.unshift(tree.pop());
          });
          stack.push(state);
          state = state.transitions[reduction[0]];
          tree.push(reduction[3](values));
        } else {
          stack.push(state);
          tree.push(token.value);
          state = state.transitions[token.symbol];
          substring = substring.substr(token.value.length);
          i += token.value.length;
        }
        
        //console.log('matched symbol '+token.symbol+' with "'+token.value+'"\n'+(token.reduce ? 'reduced' : 'shifted')+'\nremaining: "'+substring+'"');
      }
      
      return tree.pop().pop();
    };
  };
});
