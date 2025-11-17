                                                  2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y , y , y , y , y , y )                   }
                              1 2    1 3    2 3   1   2   3   4   5   6
                                2   2   2   2   2         2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y )
                                6   5   4   3   2   1 2   1
          graph => {set {0, 3}, set {3, 5}, set {0, 5}, set {1, 4}, set {2, 4}, set {1, 5}}
                                 2      3     4     5
          hSeries => 1 + 6T + 14T  + 16T  + 9T  + 2T
          hyperplanes => {a - d, d - f, a - f, b - e, c - e, b - f}
          numVariables => 6
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2-y_1*y_3-y_2*y_3, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 3}, set {3, 5}, set {0, 5}, set {1, 4}, set {2, 4}, set {1, 5}}
