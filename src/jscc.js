// Copyright 2014, Klaus Ganser <http://kganser.com>
// MIT Licensed, with this copyright and permission notice
// <http://opensource.org/licenses/MIT>

kernel.add('jscc', function() {
  return function(grammar, start, tokens) {
    
    var symbols = {}, nonterminals = Object.keys(grammar),
        firsts = {}, states = [], oldStart = start, done;

    // utility functions
    var unique = function(symbol, obj) {
      while (symbols.hasOwnProperty(symbol)) symbol += "'";
      if (obj) obj[symbol] = 1;
      return obj || symbol;
    };
    
    var merge = function(to, from, returnAdded) {
      var added;
      Object.keys(from).forEach(function(key) {
        if (!to.hasOwnProperty(key))
          added = to[key] = 1;
      });
      return returnAdded ? added : to;
    };
    
    var stringify = function(item) {
      return item[0]+' → '+item[1].map(function(symbol, i) {
        return i != item[2] ? i ? ' '+symbol : symbol : '•'+symbol;
      }).join('')+(item[2] == item[1].length ? '•' : '');
    };
    
    var getFirsts = function(production, start) {
      var symbol, current = {'': 1};
      for (var i = start || 0; (symbol = production[i]) && current.hasOwnProperty(''); i++) {
        delete current[''];
        if (grammar.hasOwnProperty(symbol)) {
          merge(current, firsts[symbol]);
        } else {
          current[symbol] = 1;
        }
      }
      return current;
    };
    
    // validate, prepare grammar
    nonterminals.forEach(function(nonterminal) {
      firsts[nonterminal] = {};
      symbols[nonterminal] = 1;
      grammar[nonterminal].forEach(function(production) {
        for (var symbol, i = 0; i < production[0].length; i++) {
          if (symbol = production[0][i]) {
            symbols[symbol] = 1;
          } else { // empty strings are reserved as EOF token
            production[0].splice(i--, 1);
          }
        }
      });
    });
    
    if (!grammar.hasOwnProperty(oldStart)) throw 'Start symbol does not appear in grammar';
    grammar[start = unique(oldStart)] = [[[oldStart], function(e) { return e; }]];
    
    Object.keys(tokens = tokens || {}).forEach(function(token) {
      tokens[token] = new RegExp(tokens[token].source.replace(/^\^?/, '^'), tokens[token].ignoreCase ? 'i' : '');
    });
    
    // compute first sets
    do {
      done = true;
      nonterminals.forEach(function(nonterminal) {
        grammar[nonterminal].forEach(function(production) {
          if (merge(firsts[nonterminal], getFirsts(production[0]), true))
            done = false;
        });
      });
    } while (!done);
    
    //firsts.forEach(function(n) { console.log('first', n, Object.keys(firsts[n])); });
    
    // adds any nonkernel productions to complete closure,
    // as well as all shifting transition symbols
    var close = function(state) {
      if (!state.transitions) state.transitions = {};
      state.reductions = {};
      do {
        done = true;
        state.items.forEach(function(item) {
          var lookaheads = {}, next = item[1][item[2]];
          if (next && !state.transitions[next]) state.transitions[next] = 0;
          if (!next || !grammar.hasOwnProperty(next)) return;
          if (Object.keys(item[3]).length && (lookaheads = getFirsts(item[1], item[2]+1)).hasOwnProperty('')) {
            delete lookaheads[''];
            merge(lookaheads, item[3]);
          }
          grammar[next].forEach(function(production) {
            var last;
            if (state.items.some(function(item) {
              last = item;
              return item[1] == production[0] && !item[2];
            })) {
              if (merge(last[3], lookaheads, true))
                done = false;
            } else {
              state.items.push([next, production[0], 0, lookaheads, production[1]]);
              done = false;
            }
          });
        });
      } while (!done);
      return state;
    };
    
    // generate LR(0) states
    states.push(close({items: [[start, grammar[start][0][0], 0, {}, grammar[start][0][1]]]}));
    
    do {
      done = true;
      states.forEach(function(state) {
        Object.keys(state.transitions).forEach(function(symbol) {
          // find all productions in state with `symbol` as
          // their next symbol and advance index; these
          // become kernel of another state, which we add
          // to `states` if it doesn't already exist
          var candidate = {items: []};
          state.items.forEach(function(item) {
            var production = item[1],
                index = item[2],
                next = production[index];
            if (next && next == symbol)
              candidate.items.push([item[0], production, index+1, {}, item[4]]);
          });
          
          //console.log('state candidate\n'+candidate.items.map(stringify).join('\n'));
          
          if (!states.some(function(state) {
            var compared = 0;
            return !state.items.some(function(item) {
              if (!item[2] && item[0] != start) return;
              compared++;
              return !candidate.items.some(function(i) {
                return item[1] == i[1] && item[2] == i[2];
              });// && !console.log(stringify(item)+' not in new state') || console.log(stringify(item)+' found in new state');
            }) && compared == candidate.items.length && (candidate = state);
          })) {
            states.push(close(candidate));
            done = false;
          }
          state.transitions[symbol] = candidate;
        });
      });
    } while (!done);
    
    // generate lookaheads for LR(0) states
    var lookaheads = [], foo = unique('#', {});
    states[0].items[0][3] = {'': 1};
    
    states.forEach(function(state) {
      state.items.forEach(function(item) {
        if (!item[2] && item[0] != start) return;
        close({items: [item.slice(0, 3).concat([foo])]}).items.forEach(function(i) {
          var next = i[1][i[2]];
          if (next) {
            state.transitions[next].items.some(function(j) {
              return i[1] == j[1] && i[2]+1 == j[2] && (next = j);
            });
            Object.keys(i[3]).forEach(function(symbol) {
              if (!foo.hasOwnProperty(symbol)) {
                next[3][symbol] = 1;
              } else if (item != next) {
                lookaheads.push([item[3], next[3]]);
              }
            });
          }
        });
      });
    });
    
    do {
      done = true;
      lookaheads.forEach(function(pair) {
        if (merge(pair[1], pair[0], true))
          done = false;
      });
    } while (!done);
    
    states.forEach(close);
    
    /*console.log(states.length+' states:\n\n'+states.map(function(state) {
      return state.items.map(stringify).join('\n');
    }).join('\n\n'));*/
    
    // detect shift-reduce, reduce-reduce conflicts
    states.forEach(function(state) {
      state.items.forEach(function(item) {
        var next = item[1][item[2]];
        if (!next) {
          Object.keys(item[3]).forEach(function(next) {
            if (state.transitions.hasOwnProperty(next)) throw 'Shift-reduce conflict on input "'+next+'"\n  '+stringify(state.transitions[next].items[0])+' (shift)\n  '+stringify(item)+' (reduce)';
            if (state.reductions.hasOwnProperty(next)) throw 'Reduce-reduce conflict on input "'+next+'"\n  '+stringify(state.reductions[next])+'\n  '+stringify(item);
            state.reductions[next] = item;
          });
        } else if (state.reductions.hasOwnProperty(next)) {
          throw 'Shift-reduce conflict on input "'+next+'"\n  '+stringify(item)+' (shift)\n  '+stringify(state.reductions[next])+' (reduce)';
        }
      });
    });
    
    return function(string) {
      var token, match, ignore = tokens[''], substring = string, values = [], stack = [], state = states[0], i = 0;
      
      while (state) {
        //console.log('now at:\n'+state.items.map(stringify).join('\n'));
        
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
            message: i == string.length ? 'Unexpected end of input' : 'Unexpected token',
            index: i,
            line: string.substring(lastNewline, (string+'\n').indexOf('\n', lastNewline)),
            row: newlines ? newlines.length+1 : 1,
            column: i - lastNewline
          };
        }
        
        if (token.reduce) {
          var args = [],
              reduction = state.reductions[token.symbol];
          for (var j = reduction[1].length; j; j--) {
            state = stack.pop();
            args.unshift(values.pop());
          }
          stack.push(state);
          state = state.transitions[reduction[0]];
          values.push(reduction[4](args));
        } else {
          stack.push(state);
          values.push(token.value);
          state = state.transitions[token.symbol];
          substring = substring.substr(token.value.length);
          i += token.value.length;
        }
        
        //console.log('matched symbol '+token.symbol+' with "'+token.value+'"\n'+(token.reduce ? 'reduced' : 'shifted')+'\nremaining: "'+substring+'"');
      }
      
      return values.pop().pop();
    };
  };
});
