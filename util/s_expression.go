// Copyright 2024 Richard Kelsey. All rights reserved.
// See file LICENSE for notices and license.

// Very basic S-expression parser.

package util

import (
	"bufio"
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode"
)

type SExpKindT int

const (
	SExpInt SExpKindT = iota
	SExpSymbol
	SExpList
)

type SExpT struct {
	Kind    SExpKindT
	Integer int
	Symbol  string
	List    []*SExpT
}

func (sexp *SExpT) String() string {
	switch sexp.Kind {
	case SExpInt:
		return fmt.Sprintf("%d", sexp.Integer)
	case SExpSymbol:
		return sexp.Symbol
	case SExpList:
		if len(sexp.List) == 0 {
			return "()"
		}
		result := "(" + sexp.List[0].String()
		for _, s := range sexp.List[1:] {
			result += " " + s.String()
		}
		return result + ")"
	}
	panic("bad S-expression")
}

func ParseSExp(data string) *SExpT {
	tokens := tokenizer(data)
	var recur func(list *SExpT) *SExpT
	recur = func(list *SExpT) *SExpT {
		for {
			next := tokens()
			if next == "\x29" {
				if list == nil {
					panic("unexpected '\x29'")
				} else {
					return nil
				}
			}
			nextSExp := &SExpT{}
			if next == "\x28" {
				nextSExp.Kind = SExpList
				recur(nextSExp)
			} else {
				i, err := strconv.Atoi(next)
				if err == nil {
					nextSExp.Kind = SExpInt
					nextSExp.Integer = i
				} else {
					nextSExp.Kind = SExpSymbol
					nextSExp.Symbol = next
				}
			}
			if list == nil {
				return nextSExp
			}
			list.List = append(list.List, nextSExp)
		}
	}
	return recur(nil)
}

func tokenizer(data string) func() string {
	reader := bufio.NewReader(strings.NewReader(data))
	return func() string {
		return nextToken(reader)
	}
}

func nextToken(reader *bufio.Reader) string {
	var contents strings.Builder
	readingInteger := false
	readingSymbol := false
	for {
		c, _, err := reader.ReadRune()
		if readingInteger {
			if err != nil || !unicode.IsDigit(c) {
				reader.UnreadRune()
				return contents.String()
			} else {
				contents.WriteRune(c)
				continue
			}
		} else if readingSymbol {
			if err != nil || !isSymbolConstituent(c) {
				reader.UnreadRune()
				return contents.String()
			} else {
				contents.WriteRune(c)
				continue
			}
		} else if err == io.EOF {
			return ""
		} else if err != nil {
			panic(err)
		} else if unicode.IsSpace(c) {
			continue
		} else if c == '\x28' {
			return "\x28"
		} else if c == '\x29' {
			return "\x29"
		} else if unicode.IsDigit(c) {
			contents.WriteRune(c)
			readingInteger = true
			continue
		} else if isSymbolConstituent(c) {
			contents.WriteRune(c)
			readingSymbol = true
			continue
		}
		panic("Unrecognized s-expression character " + strconv.QuoteRune(c))
	}
}

func isSymbolConstituent(r rune) bool {
	return unicode.IsLetter(r) || unicode.IsDigit(r) || r == ':' || r == '_' || r == '*' || r == '&'
}

/*
func main() {
    data := `(abstract std::vec::Vec (T)
              (struct std::vec::Vec
                (0 (struct RawVec
                      (0 (transparent Unique (transparent NonNull (pointer T))))
                      (1 u64)))
                (1 usize)))`
    sexp := ParseSExp(data)
    fmt.Printf("%s\n", sexp)
}
*/
