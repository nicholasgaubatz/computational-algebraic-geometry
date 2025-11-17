                                 2   2   2   2
HashTable{AOTideal => ideal (0, y , y , y , y )                    }
                                 1   2   3   4
                                2   2   2   2
          AOTinIdeal => ideal (y , y , y , y )
                                4   3   2   1
          graph => {set {0, 3}, set {0, 5}, set {1, 4}, set {2, 5}}
                                2     3    4
          hSeries => 1 + 4T + 6T  + 4T  + T
          hyperplanes => {a - d, a - f, b - e, c - f}
          numVariables => 4
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_4]
AOTideal = ideal map(R^1,R^{{0}, {-2}, {-2}, {-2}, {-2}},{{0, y_1^2, y_2^2, y_3^2, y_4^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}},{{y_4^2, y_3^2, y_2^2, y_1^2}})
G = graph {set {0, 3}, set {0, 5}, set {1, 4}, set {2, 5}}
