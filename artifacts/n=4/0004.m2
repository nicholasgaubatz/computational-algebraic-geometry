                                 2   2   2
HashTable{AOTideal => ideal (0, y , y , y )            }
                                 1   2   3
                                2   2   2
          AOTinIdeal => ideal (y , y , y )
                                3   2   1
          graph => {set {0, 2}, set {0, 3}, set {1, 3}}
                                2    3
          hSeries => 1 + 3T + 3T  + T
          hyperplanes => {a - c, a - d, b - d}
          numVariables => 3
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_3]
AOTideal = ideal map(R^1,R^{{0}, {-2}, {-2}, {-2}},{{0, y_1^2, y_2^2, y_3^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}},{{y_3^2, y_2^2, y_1^2}})
G = graph {set {0, 2}, set {0, 3}, set {1, 3}}
