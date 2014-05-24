// Copyright 2014, Klaus Ganser <http://kganser.com>
// MIT Licensed, with this copyright and permission notice
// <http://opensource.org/licenses/MIT>

kernel.add('jscc', function() {
  return function(grammar, start, tokens) {
    
    var terminals = {}, nonterminals = Object.keys(grammar),
        firsts = {}, items = [], oldStart = start, done;

    // utility functions
    var unique = function(symbol, obj) {
      while (grammar.hasOwnProperty(symbol)) symbol += "'";
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
    
    var stringify = function(state) {
      return state[0]+' → '+state[1].map(function(symbol, i) {
        return i != state[2] ? i ? ' '+symbol : symbol : '•'+symbol;
      }).join('')+(state[2] == state[1].length ? '•' : '');
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
    if (!grammar.hasOwnProperty(oldStart)) throw 'Start symbol does not appear in grammar';
    grammar[start = unique(oldStart)] = [[[oldStart], function(e) { return e; }]];
    
    Object.keys(tokens = tokens || {}).forEach(function(token) {
      tokens[token] = new RegExp(tokens[token].source.replace(/^\^?/, '^'), tokens[token].ignoreCase ? 'i' : '');
    });
    
    nonterminals.forEach(function(nonterminal) {
      firsts[nonterminal] = {};
      grammar[nonterminal].forEach(function(production) {
        production[0].forEach(function(symbol, i) {
          if (!symbol) // empty strings are reserved as EOF token
            return production[0].splice(i, 1);
          if (!grammar.hasOwnProperty(symbol))
            terminals[symbol] = 1;
        });
      });
    });
    terminals = Object.keys(terminals);
    
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
    var close = function(item) {
      if (!item.transitions) item.transitions = {};
      item.reductions = {};
      do {
        done = true;
        item.state.forEach(function(state) {
          var lookaheads = {}, next = state[1][state[2]];
          if (next && !item.transitions[next]) item.transitions[next] = 0;
          if (!next || !grammar.hasOwnProperty(next)) return;
          if (Object.keys(state[3]).length && (lookaheads = getFirsts(state[1], state[2]+1)).hasOwnProperty('')) {
            delete lookaheads[''];
            merge(lookaheads, state[3]);
          }
          grammar[next].forEach(function(production) {
            var last;
            if (item.state.some(function(state) {
              last = state;
              return state[1] == production[0] && !state[2];
            })) {
              if (merge(last[3], lookaheads, true))
                done = false;
            } else {
              item.state.push([next, production[0], 0, lookaheads, production[1]]);
              done = false;
            }
          });
        });
      } while (!done);
      return item;
    };
    
    // generate LR(0) states
    items.push(close({state: [[start, grammar[start][0][0], 0, {}, grammar[start][0][1]]]}));
    
    do {
      done = true;
      items.forEach(function(item) {
        Object.keys(item.transitions).forEach(function(symbol) {
          // find all productions in item with `symbol` as
          // their next symbol and advance index; these
          // become kernel of another item, which we add
          // to `items` if it doesn't already exist
          var candidate = {state: []};
          item.state.forEach(function(state) {
            var production = state[1],
                index = state[2],
                next = production[index];
            if (next && next == symbol)
              candidate.state.push([state[0], production, index+1, {}, state[4]]);
          });
          
          //console.log('item candidate\n'+candidate.state.map(stringify).join('\n'));
          
          if (!items.some(function(item) {
            var compared = 0;
            return !item.state.some(function(state) {
              if (!state[2] && state[0] != start) return;
              compared++;
              return !candidate.state.some(function(s) {
                return state[1] == s[1] && state[2] == s[2];
              });// && (console.log(stringify(state)+' not in new item') || true) || console.log(stringify(state)+' found in new item');
            }) && compared == candidate.state.length && (candidate = item);
          })) {
            items.push(close(candidate));
            done = false;
          }
          item.transitions[symbol] = candidate;
        });
      });
    } while (!done);
    
    // generate lookaheads for LR(0) states
    var lookaheads = [], foo = unique('#', {});
    items[0].state[0][3] = {'': 1};
    
    items.forEach(function(item) {
      item.state.forEach(function(state) {
        if (!state[2] && state[0] != start) return;
        close({state: [state.slice(0, 3).concat([foo])]}).state.forEach(function(s) {
          var next = s[1][s[2]];
          if (next) {
            item.transitions[next].state.some(function(t) {
              return t[1] == s[1] && t[2] == s[2]+1 && (next = t);
            });
            Object.keys(s[3]).forEach(function(symbol) {
              if (!foo.hasOwnProperty(symbol)) {
                next[3][symbol] = 1;
              } else if (state != next) {
                lookaheads.push([state[3], next[3]]);
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
    
    items.forEach(close);
    
    /*console.log(items.length+' items:\n\n'+items.map(function(item) {
      return item.state.map(stringify).join('\n');
    }).join('\n\n'));*/
    
    // detect shift-reduce, reduce-reduce conflicts
    items.forEach(function(item) {
      item.state.forEach(function(state) {
        var next = state[1][state[2]];
        if (next) {
          if (item.reductions.hasOwnProperty(next)) throw 'Shift-reduce conflict on input "'+next+'"\n  '+stringify(state)+' (shift)\n  '+stringify(item.reductions[next])+' (reduce)';
        } else {
          Object.keys(state[3]).forEach(function(next) {
            if (item.transitions.hasOwnProperty(next)) throw 'Shift-reduce conflict on input "'+next+'"\n  '+stringify(item.transitions[next].state[0])+' (shift)\n  '+stringify(state)+' (reduce)';
            if (item.reductions.hasOwnProperty(next)) throw 'Reduce-reduce conflict on input "'+next+'"\n  '+stringify(item.reductions[next])+'\n  '+stringify(state);
            item.reductions[next] = state;
          });
        }
      });
    });
    
    return function(string) {
      var token, match, ignore = tokens[''], substring = string, tree = [], stack = [], item = items[0], i = 0;
      
      while (item) {
        //console.log('now at:\n'+item.state.map(stringify).join('\n'));
        
        token = undefined;
        
        if (ignore && (match = ignore.exec(substring))) {
          substring = substring.substr(match[0].length);
          i += match[0].length;
          continue;
        }
        
        (function(process) {
          Object.keys(item.transitions).forEach(process(false));
          Object.keys(item.reductions).forEach(process(true));
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
          throw 'error' || {
            message: i == string.length ? 'Unexpected end of input' : 'Unexpected token',
            index: i,
            line: string.substring(lastNewline, (string+'\n').indexOf('\n', lastNewline)),
            row: newlines ? newlines.length+1 : 1,
            column: i - lastNewline
          };
        }
        
        if (token.reduce) {
          var values = [],
              reduction = item.reductions[token.symbol];
          for (var j = reduction[1].length; j; j--) {
            item = stack.pop();
            values.unshift(tree.pop());
          }
          stack.push(item);
          item = item.transitions[reduction[0]];
          tree.push(reduction[4](values));
        } else {
          stack.push(item);
          tree.push(token.value);
          item = item.transitions[token.symbol];
          substring = substring.substr(token.value.length);
          i += token.value.length;
        }
        
        //console.log('matched symbol '+token.symbol+' with "'+token.value+'"\n'+(token.reduce ? 'reduced' : 'shifted')+'\nremaining: "'+substring+'"');
      }
      
      return tree.pop().pop();
    };
  };
});
