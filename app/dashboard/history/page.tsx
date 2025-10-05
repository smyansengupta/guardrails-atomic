import { currentUser } from '@clerk/nextjs/server';
import { redirect } from 'next/navigation';
import { listVerificationLogs } from '@/lib/history/persistence';
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from '@/components/ui/card';
import { HistoryList } from '@/components/history/HistoryList';

export const dynamic = 'force-dynamic';

export default async function HistoryPage() {
  const user = await currentUser();

  if (!user) {
    redirect('/sign-in?redirect_url=/dashboard/history');
  }

  const userId = user.id;

  try {
    const history = await listVerificationLogs(userId, 20);

    return (
      <div className="space-y-6">
        <Card>
          <CardHeader>
            <CardTitle>Verification History</CardTitle>
            <CardDescription>
              Review previous specifications, generated code, and proof reports. New entries appear as you complete fully
              verified runs.
            </CardDescription>
          </CardHeader>
          <CardContent>
            <p className="text-sm text-muted-foreground">
              History is scoped to your Clerk account. Data is persisted in MongoDB Atlas.
            </p>
          </CardContent>
        </Card>

        <HistoryList initialItems={history.items} initialNextCursor={history.nextCursor} />
      </div>
    );
  } catch (error) {
    console.error('Failed to render history page:', error);
    return (
      <Card>
        <CardHeader>
          <CardTitle>Verification History</CardTitle>
          <CardDescription>We could not load your history right now. Please try again later.</CardDescription>
        </CardHeader>
      </Card>
    );
  }
}
