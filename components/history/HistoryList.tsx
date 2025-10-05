"use client";

import { useState } from 'react';
import { VerificationLogRecord } from '@/lib/history/persistence';
import { Card, CardContent, CardFooter, CardHeader, CardTitle } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Button } from '@/components/ui/button';
import { Spinner } from '@/components/ui/spinner';

interface HistoryListProps {
  initialItems: VerificationLogRecord[];
  initialNextCursor?: string;
}

export function HistoryList({ initialItems, initialNextCursor }: HistoryListProps) {
  const [items, setItems] = useState(initialItems);
  const [nextCursor, setNextCursor] = useState<string | undefined>(initialNextCursor);
  const [loadingMore, setLoadingMore] = useState(false);
  const [expandedId, setExpandedId] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);

  const toggleExpanded = (id: string) => {
    setExpandedId((current) => (current === id ? null : id));
  };

  const loadMore = async () => {
    if (!nextCursor) return;

    setLoadingMore(true);
    setError(null);

    try {
      const response = await fetch(`/api/history?cursor=${nextCursor}`, {
        method: 'GET',
        cache: 'no-store',
      });

      if (!response.ok) {
        throw new Error('Failed to load more history');
      }

      const data: { items: VerificationLogRecord[]; nextCursor?: string } = await response.json();
      setItems((prev) => [...prev, ...data.items]);
      setNextCursor(data.nextCursor);
    } catch (fetchError) {
      const message = fetchError instanceof Error ? fetchError.message : 'Unknown error';
      setError(message);
    } finally {
      setLoadingMore(false);
    }
  };

  if (items.length === 0) {
    return (
      <Card>
        <CardHeader>
          <CardTitle>No verification runs yet</CardTitle>
        </CardHeader>
        <CardContent>
          <p className="text-sm text-muted-foreground">
            Run your first verification to see it appear here. Past specifications, code, and proof details will be
            available once generated.
          </p>
        </CardContent>
      </Card>
    );
  }

  return (
    <div className="space-y-4">
      {items.map((item) => {
        const dateLabel = new Date(item.createdAt).toLocaleString();
        const statusVariant = item.success ? 'default' : 'destructive';
        const duration = item.durationMs ? `${Math.round(item.durationMs)} ms` : '—';

        return (
          <Card key={item.id} className="border-muted">
            <CardHeader className="flex flex-row items-center justify-between space-y-0">
              <div>
                <CardTitle className="text-base">
                  {item.specName ?? 'Untitled specification'}
                </CardTitle>
                <p className="text-xs text-muted-foreground">{dateLabel}</p>
              </div>
              <Badge variant={statusVariant}>{item.success ? 'Verified' : 'Failed'}</Badge>
            </CardHeader>
            <CardContent className="space-y-2 text-sm">
              <div className="flex flex-wrap gap-4 text-xs text-muted-foreground">
                <span>Iterations: {item.iterations}</span>
                <span>Duration: {duration}</span>
                <span>States explored: {item.result.proofReport?.statesExplored ?? '—'}</span>
              </div>
              <pre className="max-h-32 overflow-auto rounded bg-muted p-3 text-xs text-muted-foreground">
                {item.spec.trim()}
              </pre>

              {expandedId === item.id && (
                <div className="space-y-3">
                  {item.result.finalCode && (
                    <section>
                      <h3 className="mb-1 text-sm font-semibold">Final Code</h3>
                      <pre className="max-h-64 overflow-auto rounded bg-background p-3 text-xs">
                        {item.result.finalCode}
                      </pre>
                    </section>
                  )}

                  {item.result.proofReport && (
                    <section className="text-xs text-muted-foreground">
                      <h3 className="mb-1 text-sm font-semibold text-foreground">Proof Report</h3>
                      <p>Invariants: {item.result.proofReport.invariantsVerified.join(', ') || '—'}</p>
                      <p>Fault Scenarios: {item.result.proofReport.faultScenariosChecked.join(', ') || '—'}</p>
                    </section>
                  )}

                  {item.result.error && (
                    <section className="text-xs text-red-500">
                      <h3 className="mb-1 text-sm font-semibold text-red-500">Errors</h3>
                      <p>{item.result.error}</p>
                    </section>
                  )}
                </div>
              )}
            </CardContent>
            <CardFooter className="flex items-center justify-between">
              <Button variant="outline" size="sm" onClick={() => toggleExpanded(item.id)}>
                {expandedId === item.id ? 'Hide details' : 'View details'}
              </Button>
            </CardFooter>
          </Card>
        );
      })}

      {error && <p className="text-sm text-destructive">{error}</p>}

      {nextCursor && (
        <div className="flex justify-center pt-2">
          <Button variant="secondary" size="sm" onClick={loadMore} disabled={loadingMore} className="min-w-[150px]">
            {loadingMore ? (
              <span className="flex items-center gap-2">
                <Spinner size="xs" /> Loading...
              </span>
            ) : (
              'Load more'
            )}
          </Button>
        </div>
      )}
    </div>
  );
}
