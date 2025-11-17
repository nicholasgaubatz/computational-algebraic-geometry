                                                  2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y , y , y , y , y )           }
                              1 3    1 4    3 4   1   2   3   4   5
                                2   2   2         2   2
          AOTinIdeal => ideal (y , y , y , y y , y , y )
                                5   4   3   1 3   2   1
          graph => {set {0, 3}, set {1, 3}, set {3, 4}, set {0, 4}, set {2, 4}}
                                2     3     4
          hSeries => 1 + 5T + 9T  + 7T  + 2T
          hyperplanes => {a - d, b - d, d - e, a - e, c - e}
          numVariables => 5
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_5]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_3-y_1*y_4-y_3*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1^2}})
G = graph {set {0, 3}, set {1, 3}, set {3, 4}, set {0, 4}, set {2, 4}}
