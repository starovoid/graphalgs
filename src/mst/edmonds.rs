pub use petgraph::algo::FloatMeasure;
use petgraph::graph::Graph;
use petgraph::unionfind::UnionFind;
use petgraph::visit::{
    EdgeRef, IntoEdgeReferences, IntoEdges, IntoNodeIdentifiers, NodeCount, NodeIndexable,
};

/*
Проверяем, можно ли дойти из v до остальных вершин. Если можно - запускаем findMST.

int findMST(edges, n, root):
   int res = 0
   int minEdge[n] // создаем массив минимумов, входящих в каждую компоненту, инициализируем бесконечностью.
   for each e∈ edges
       minEdge[e.to] = min(e.w, minEdge[e.to])
   for each v∈V∖{root}
       res += minEdge[v] //веса минимальных ребер точно будут в результате
   edge zeroEdges[] //создаем массив нулевых ребер
   for each e∈ edges
       if e.w == minEdge[e.to]
           zeroEdges.pushback(e1) // e1 - ребро е, уменьшенное на минимальный вес, входящий в e.to
   if dfs(root, zeroEdges) // проверяем, можно ли дойти до всех вершин по нулевым ребрам
       return res
   int newComponents[n] // будущие компоненты связности
   newComponents = Сondensation(zeroEdges)
   edge newEdges[] //создаем массив ребер в новом графе с вершинами в полученных компонентах
   for each e∈ edges
       if e.to и e.from в разных компонентах
           добавляем в newEdges ребро с концами в данных компонентах и весом e.w - minEdge[e.to]
   res += findMST(newEdges, ComponentsCount, newComponents[root])
   return res
   ------------------------------------------------------------------------

   for (ll v = 0; v < n; ++v) {
    if (dsu.check(v, 0)) { // проверяем, что вершина ещё недостижима из корня
        continue;
    }
    ++timer; // быстрое обнуление used-а
    vector<ll> path; // будем хранить пройденный путь
    path.emplace_back(v);
    while (!dsu.check(path.back(), 0)) { // проверяем, что ещё не дошли до корня
        ll v = dsu.get(path.back()); // берём последнюю вершину пути
        used[v] = timer;
        while (dsu.check(graph[v].begin()->second, v)) {
            graph[v].erase(graph[v].begin()); // удаляем петли
        }
        ll u = dsu.get(graph[v].begin()->second); // получаем следующую вершину пути
        result += graph[v].begin()->first + delta[v]; // прибавляем к ответу вес ребра
        delta[v] -= graph[v].begin()->first + delta[v]; // вычитаем из всех ребер ведущих в $v$ вес ребра
        if (used[u] != timer) {
            path.emplace_back(u);
            continue;
        }
        while (!dsu.check(path.back(), u)) { // удаляем цикл
            dsu.merge(path.back(), u); // внутри этой функции я так же объединяю множества рёбер
            path.pop_back();
        }
    }
    while (!path.empty()) { // проставляем всем посещённым вершинам, что они достижимы из корня
        dsu.merge(s.back(), 0);
        path.pop_back();
    }
}
*/
pub fn chu_liu_edmonds<G, F, K>(graph: G, root: usize, mut edge_cost: F) -> Vec<G::EdgeId>
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount + IntoEdges,
    F: FnMut(G::EdgeRef) -> K,
    K: FloatMeasure,
{
    println!("{}", reachability(graph, root));
    Vec::new()
}

/// Сheck whether all vertices of the graph are reachable from the **root** vertex.
fn reachability<G>(graph: G, root: usize) -> bool
where
    G: IntoEdgeReferences + IntoNodeIdentifiers + NodeIndexable + NodeCount + IntoEdges,
{
    let mut visited = vec![false; graph.node_count()];
    visited[root] = true;
    let mut stack = Vec::new();
    stack.push(root);

    while let Some(node) = stack.pop() {
        for to in graph.neighbors(graph.from_index(node)) {
            let to = graph.to_index(to);
            if !visited[to] {
                stack.push(to);
                visited[to] = true;
            }
        }
    }

    visited.into_iter().all(|v| v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::EdgeIndex;
    use petgraph::graph::Graph;
    use std::collections::HashSet;

    #[test]
    #[allow(unused)]
    fn test_chu_liu_edmonds() {
        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());
        let n4 = graph.add_node(());

        let e1 = graph.add_edge(n0, n1, 5.0);
        let e2 = graph.add_edge(n0, n2, 5.0);
        let e3 = graph.add_edge(n2, n1, 2.0);
        let e4 = graph.add_edge(n1, n3, 1.0);
        let e5 = graph.add_edge(n3, n1, 1.0);
        let e6 = graph.add_edge(n2, n4, 1.0);
        let e7 = graph.add_edge(n4, n2, 1.0);
        let e8 = graph.add_edge(n3, n4, 2.0);

        assert_eq!(
            chu_liu_edmonds(&graph, 0, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e1, e4, e8, e7]),
        );

        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());

        let e1 = graph.add_edge(n0, n1, 4.0);
        let e2 = graph.add_edge(n0, n2, 5.0);
        let e3 = graph.add_edge(n2, n1, 1.0);
        let e4 = graph.add_edge(n1, n2, 3.0);
        let e5 = graph.add_edge(n3, n1, 6.0);

        assert_eq!(chu_liu_edmonds(&graph, 0, |edge| *edge.weight()), vec![],);

        let e6 = graph.add_edge(n2, n3, 7.0);

        assert_eq!(
            chu_liu_edmonds(&graph, 0, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e2, e3, e6]),
        );
        assert_eq!(chu_liu_edmonds(&graph, 1, |edge| *edge.weight()), vec![],);
        assert_eq!(chu_liu_edmonds(&graph, 2, |edge| *edge.weight()), vec![],);
        assert_eq!(chu_liu_edmonds(&graph, 3, |edge| *edge.weight()), vec![],);

        let mut graph = Graph::<(), f32>::new();
        let n0 = graph.add_node(());
        let n1 = graph.add_node(());
        let n2 = graph.add_node(());
        let n3 = graph.add_node(());
        let n4 = graph.add_node(());
        let n5 = graph.add_node(());

        let e1 = graph.add_edge(n0, n2, -9.0);
        let e2 = graph.add_edge(n0, n3, 4.0);
        let e3 = graph.add_edge(n1, n5, 8.0);
        let e4 = graph.add_edge(n3, n5, 6.0);
        let e5 = graph.add_edge(n4, n0, 1.0);
        let e6 = graph.add_edge(n4, n0, -6.0);
        let e7 = graph.add_edge(n4, n2, -14.0);
        let e8 = graph.add_edge(n4, n1, -1.0);
        let e9 = graph.add_edge(n5, n4, -2.0);

        assert_eq!(
            chu_liu_edmonds(&graph, 0, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e2, e4, e9, e8, e7]),
        );
        assert_eq!(chu_liu_edmonds(&graph, 1, |edge| *edge.weight()), vec![],);
        assert_eq!(
            chu_liu_edmonds(&graph, 2, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e4, e9, e6, e8, e7]),
        );
        assert_eq!(
            chu_liu_edmonds(&graph, 3, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e4, e9, e6, e8, e7]),
        );
        assert_eq!(
            chu_liu_edmonds(&graph, 4, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e5, e8, e3, e7, e2]),
        );
        assert_eq!(
            chu_liu_edmonds(&graph, 5, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e9, e8, e6, e2, e7]),
        );

        let mut graph = Graph::<(), f32>::new();
        assert_eq!(chu_liu_edmonds(&graph, 0, |edge| *edge.weight()), vec![],);

        let n0 = graph.add_node(());
        assert_eq!(chu_liu_edmonds(&graph, 0, |edge| *edge.weight()), vec![],);

        let n1 = graph.add_node(());
        assert_eq!(chu_liu_edmonds(&graph, 0, |edge| *edge.weight()), vec![],);

        let e1 = graph.add_edge(n0, n1, 42.0);
        assert_eq!(chu_liu_edmonds(&graph, 0, |edge| *edge.weight()), vec![e1],);

        let n2 = graph.add_node(());
        assert_eq!(chu_liu_edmonds(&graph, 0, |edge| *edge.weight()), vec![],);

        let e2 = graph.add_edge(n1, n2, 32.0);
        let e3 = graph.add_edge(n2, n0, 22.0);
        assert_eq!(
            chu_liu_edmonds(&graph, 0, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e1, e2]),
        );
        assert_eq!(
            chu_liu_edmonds(&graph, 1, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e2, e3]),
        );
        assert_eq!(
            chu_liu_edmonds(&graph, 2, |edge| *edge.weight())
                .into_iter()
                .collect::<HashSet<EdgeIndex>>(),
            HashSet::from([e3, e1]),
        );
    }
}
